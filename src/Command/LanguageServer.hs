{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Command.LanguageServer where

import Control.Concurrent.STM as STM
import Data.Aeson (ToJSON)
import Data.Default (def)
import Data.Foldable
import Data.Monoid
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Language.Haskell.LSP.Control as LSP
import qualified Language.Haskell.LSP.Core as LSP
import qualified Language.Haskell.LSP.TH.DataTypesJSON as LSP
import qualified Language.Haskell.LSP.VFS as LSP
import Options.Applicative
import qualified Yi.Rope as Yi

import qualified Processor.Files as Processor
import Syntax.Concrete.Scoped (ProbePos(..))

type params ~> response = LSP.LspFuncs () -> params -> IO (Maybe response)
type Notified params = LSP.LspFuncs () -> params -> IO ()

sendNotification :: LSP.LspFuncs c -> String -> IO ()
sendNotification lf s =
  LSP.sendFunc lf
    (LSP.NotificationMessage "2.0" LSP.WindowLogMessage
      (LSP.LogMessageParams LSP.MtInfo (T.pack s)))

fileContents :: LSP.LspFuncs () -> LSP.Uri -> IO Text
fileContents lf uri = do
  mvf <- LSP.getVirtualFileFunc lf uri
  case mvf of
    Just (LSP.VirtualFile _ rope) -> return (Yi.toText rope)
    Nothing ->
      case LSP.uriToFilePath uri of
        Just fp -> T.readFile fp
        Nothing -> return "Command.LanguageServer.fileContents: file missing"

hover :: LSP.TextDocumentPositionParams ~> LSP.Hover
hover lf (LSP.TextDocumentPositionParams (LSP.TextDocumentIdentifier uri) (LSP.Position line char)) = do
  contents <- fileContents lf uri
  let LSP.Uri uri_text = uri
  let uri_str = T.unpack uri_text
  res <- Processor.vfsCheck (pure (uri_str, contents)) (ProbePos uri_str line char)
  return $ Just LSP.Hover {
    _contents = LSP.List [ LSP.PlainString msg | msg <- fold res ],
    _range = Nothing
  }

server :: IO ()
server = do
  lsp_funcs_ref <- STM.newTVarIO (Nothing :: Maybe (LSP.LspFuncs ()))

  let handle
        :: ToJSON response => params ~> response
        -> Maybe (LSP.Handler (LSP.RequestMessage method params response))
      handle h = Just $ \ (LSP.RequestMessage jsonrpc req_id _method params) -> do
        Just lf <- STM.readTVarIO lsp_funcs_ref
        mresponse <- h lf params
        case mresponse of
          Just response ->
            LSP.sendFunc lf (LSP.ResponseMessage jsonrpc (LSP.responseId req_id) (Just response) Nothing)
          Nothing -> return ()

  -- let notified
  --       :: Notified params
  --       -> Maybe (LSP.Handler (LSP.NotificationMessage method params))
  --     notified h = Just $ \ (LSP.NotificationMessage _jsonrpc _method params) -> do
  --       Just lf <- STM.readTVarIO lsp_funcs_ref
  --       h lf params

  LSP.run
    (\ _ -> Right (), \ lf -> STM.atomically (STM.writeTVar lsp_funcs_ref (Just lf)) >> return Nothing)
    (def {
      LSP.hoverHandler = handle hover
    })
    def
  return ()




optionsParserInfo :: ParserInfo ()
optionsParserInfo = info (pure ())
  $ fullDesc
  <> progDesc "Start a language server"
  <> header "sixten lsp"

command :: ParserInfo (IO ())
command = const server <$> optionsParserInfo


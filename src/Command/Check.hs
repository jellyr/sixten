{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
module Command.Check where

import Data.Monoid
import qualified Data.Text.IO as Text
import Options.Applicative
import System.IO
import Util

import qualified Backend.Target as Target
import Command.Check.Options
import Error
import qualified Processor.Files as Processor
import qualified Processor.Result as Processor

import Data.List.Split as Split

import qualified Syntax.Concrete.Scoped as Scoped

optionsParserInfo :: ParserInfo Options
optionsParserInfo = info (helper <*> optionsParser)
  $ fullDesc
  <> progDesc "Type check a Sixten program"
  <> header "sixten check"

optionsParser :: Parser Options
optionsParser = Options
  <$> nonEmptySome (strArgument
    $ metavar "FILES..."
    <> help "Input source FILES"
    <> action "file"
    )
  <*> option auto
    (long "verbose"
    <> short 'v'
    <> metavar "LEVEL"
    <> help "Set the verbosity level to LEVEL"
    <> value 0
    <> completeWith ["0", "10", "20", "30", "40"]
    )
  <*> optional (strOption
    $ long "log-file"
    <> metavar "FILE"
    <> help "Write logs to FILE instead of standard output"
    <> action "file"
    )
  <*> optional (option parseProbePos
    $ long "probe"
    <> metavar "FILE:LINE:COL"
    <> help "Probe information at a position in the program"
    <> action "file"
    )
  where
    parseProbePos :: ReadM Scoped.ProbePos
    parseProbePos = eitherReader $ \ s ->
      case Split.splitOn ":" s of
        [file, sline, scol]
          | [(line, "")] <- reads sline,
            [(col, "")] <- reads scol
          -> Right (Scoped.ProbePos file (line-1) (col-1))
        _ -> Left $ "Use format FILE:LINE:COL, you wrote: " ++ s

check
  :: Options
  -> IO ()
check opts = withLogHandle (logFile opts) $ \logHandle -> do
  procResult <- Processor.checkFiles Processor.Arguments
        { Processor.sourceFiles = inputFiles opts
        , Processor.assemblyDir = ""
        , Processor.target = Target.defaultTarget
        , Processor.logHandle = logHandle
        , Processor.verbosity = verbosity opts
        , Processor.probePos = probePos opts
        }
  case procResult of
    Processor.Failure errs -> mapM_ printError errs
    Processor.Success _ -> Text.putStrLn "Type checking completed successfully"
  where
    withLogHandle Nothing k = k stdout
    withLogHandle (Just file) k = Util.withFile file WriteMode k

command :: ParserInfo (IO ())
command = check <$> optionsParserInfo

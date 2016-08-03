{-# LANGUAGE OverloadedStrings #-}
module Main where

import qualified Bound.Scope.Simple as Simple
import Control.Monad.Except
import Control.Monad.State
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List
import Data.Monoid
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Data.Vector as V
import Data.Void
import System.Environment
import System.IO

import Builtin
import Close
import ClosureConvert
import Erase
import qualified Generate
import Infer
import Lift
import qualified LLVM
import Meta
import TCM
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Closed as Closed
import qualified Syntax.Concrete as Concrete
import qualified Syntax.Converted as Converted
import qualified Syntax.Lifted as Lifted
import qualified Syntax.Parse as Parse
import qualified Syntax.Resolve as Resolve
import qualified Syntax.SLambda as SLambda
import Util

processGroup
  :: [(Name, Definition Concrete.Expr Name, Concrete.Expr Name)]
  -> TCM s [(Name, LLVM.B)]
processGroup
  = exposeGroup
  >=> typeCheckGroup
  >=> addGroupToContext
  >=> eraseGroup
  >=> closeGroup
  >=> closureConvertGroup
  >=> processConvertedGroup

processConvertedGroup
  :: [(Name, Converted.SExpr Void)]
  -> TCM s [(Name, LLVM.B)]
processConvertedGroup
  = liftGroup
  >=> generateGroup

exposeGroup
  :: [(Name, Definition Concrete.Expr Name, Concrete.Expr Name)]
  -> TCM s [(Name, Definition Concrete.Expr (Var Int v), Scope Int Concrete.Expr v)]
exposeGroup defs = return
  [ ( n
    , s >>>= unvar (pure . B) Concrete.Global
    , t >>>= Concrete.Global
    )
  | ((s, t), (n, _, _)) <- zip (zip abstractedScopes abstractedTypes) defs]
  where
    abstractedScopes = recursiveAbstractDefs [(n, d) | (n, d, _) <- defs]
    abstractedTypes = recursiveAbstract [(n, t) | (n, _, t) <- defs]

typeCheckGroup
  :: [(Name, Definition Concrete.Expr (Var Int (MetaVar Abstract.Expr s)), ScopeM Int Concrete.Expr s)]
  -> TCM s [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
typeCheckGroup defs = do
  checkedDefs <- checkRecursiveDefs $ V.fromList defs

  let vf :: MetaVar Abstract.Expr s -> TCM s b
      vf v = throwError $ "typeCheckGroup " ++ show v
  checkedDefs' <- traverse (bitraverse (traverse $ traverse vf) (traverse vf)) checkedDefs
  let names = V.fromList [n | (n, _, _) <- defs]
      instDefs =
        [ ( names V.! i
          , instantiateDef (Abstract.Global . (names V.!)) d
          , instantiate (Abstract.Global . (names V.!)) t
          )
        | (i, (d, t)) <- zip [0..] $ V.toList checkedDefs'
        ]
  return instDefs

addGroupToContext
  :: [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
  -> TCM s [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)]
addGroupToContext defs = do
  addContext $ HM.fromList $ (\(n, d, t) -> (n, (d, t))) <$> defs
  return defs

eraseGroup
  :: [(Name, Definition Abstract.Expr Void, Abstract.Expr Void)] 
  -> TCM s [(Name, Definition SLambda.SExpr Void)]
eraseGroup defs = forM defs $ \(x, e, _) -> (,) x <$> eraseDef e

closeGroup
  :: [(Name, Definition SLambda.SExpr Void)]
  -> TCM s [(Name, Closed.SExpr Void)]
closeGroup defs = sequence
  [ do
      e' <- closeSExpr $ vacuous e
      e'' <- traverse (throwError . ("closeGroup " ++) . show) e'
      return (x, e'')
  | (x, Definition e) <- defs
  ]

closureConvertGroup
  :: [(Name, Closed.SExpr Void)]
  -> TCM s [(Name, Converted.SExpr Void)]
closureConvertGroup defs = do
  sigs <- forM defs $ \(x, e) -> (,) x <$> ClosureConvert.convertSignature (vacuous e)
  addConvertedSignatures $ HM.fromList sigs
  forM sigs $ \(x, sig) ->
    (,) x . fmap (error "closureConvertGroup conv") <$> ClosureConvert.convertBody (error "closureConvertGroup sig" <$> sig)

liftGroup
  :: [(Name, Converted.SExpr Void)]
  -> TCM s [(Name, Lifted.Definition Void)]
liftGroup defs = fmap concat $ forM defs $ \(name, e) -> do
  let (e', fs) = liftDefinition name e
  addConvertedSignatures $ HM.fromList $ fmap fakeSignature <$> fs
  return $ (name, e') : fmap (second Lifted.FunctionDef) fs
  where
    -- TODO this isn't a very nice way to do this
    fakeSignature
      :: Lifted.Function Void
      -> Converted.Signature Converted.Expr Unit Void
    fakeSignature (Lifted.Function retDir tele _body)
      = Converted.Function
        retDir
        (Telescope $ (\(h, d) -> (h, d, Simple.Scope $ Converted.Lit 0)) <$> tele)
        $ Simple.Scope Unit

generateGroup
  :: [(Name, Lifted.Definition Void)]
  -> TCM s [(LLVM.B, LLVM.B)]
generateGroup defs = do
  qcindex <- qconstructorIndex
  cxt <- gets tcConvertedSignatures
  let env = Generate.GenEnv qcindex (`HM.lookup` cxt)
  return $ flip map defs $ \(x, e) ->
    second (fold . intersperse "\n")
      $ Generate.runGen env
      $ Generate.generateDefinition x
      $ vacuous e

processFile :: FilePath -> FilePath -> IO ()
processFile file output = do
  parseResult <- Parse.parseFromFile Parse.program file
  let resolveResult = Resolve.program <$> parseResult
  case resolveResult of
    Nothing -> return ()
    Just (Left err) -> Text.putStrLn err
    Just (Right resolved) -> do
      let constrs = HS.fromList
                  $ programConstrNames Builtin.context
                  <> programConstrNames resolved
          instCon v
            | v `HS.member` constrs = Concrete.Con $ Left v
            | otherwise = pure v
          resolved' = bimap (>>>= instCon) (>>= instCon) <$> resolved
          groups = dependencyOrder resolved'
      case runTCM (process groups) mempty of
        (Left err, t) -> do
          mapM_ (putDoc . (<> "\n")) t
          putStrLn err
        (Right res, _) -> withFile output WriteMode $ \handle -> do
          let outputStrLn s = do
                Text.hPutStrLn handle s
                Text.putStrLn s
          forM_ (concat res) $ \(_, b) -> do
            outputStrLn ""
            outputStrLn b
          outputStrLn ""
          outputStrLn "define i32 @main() {"
          outputStrLn "  call void @GC_init()"
          forM_ (concat res) $ \(i, _) ->
            unless (Text.null i) $ outputStrLn i
          outputStrLn "  ret i32 0"
          outputStrLn "}"
  where
    process groups = do
      addContext Builtin.context
      addConvertedSignatures $ Converted.signature <$> Builtin.convertedContext
      builtins <- processConvertedGroup $ HM.toList Builtin.convertedContext
      results <- mapM (processGroup . fmap (\(n, (d, t)) -> (n, d, t))) groups
      return $ builtins : results

main :: IO ()
main = do
  x:y:_ <- getArgs
  processFile x y

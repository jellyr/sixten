{-# LANGUAGE FlexibleContexts #-}
module Inference.MetaVar.Zonk where

import Control.Monad.Except
import Control.Monad.ST
import Control.Monad.State
import Data.Bifoldable
import Data.Bitraversable
import Data.Function
import Data.Functor.Const
import Data.Hashable
import qualified Data.HashMap.Lazy as HashMap
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashSet as HashSet
import Data.HashSet(HashSet)
import Data.Monoid
import Data.STRef
import Data.String
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Vector(Vector)
import Data.Void

import Analysis.Simplify
import Inference.MetaVar
import MonadFresh
import Syntax
import Syntax.Abstract
import Util
import VIX

zonk :: MonadIO m => Expr MetaVar v -> m (Expr MetaVar v)
zonk = bindMetas $ \m es -> do
  sol <- solution m
  case sol of
    Left _ -> return $ Meta m es
    Right e -> return $ betaApps (vacuous e) es

metaVars :: MonadIO m => Expr MetaVar v -> m (HashSet MetaVar)
metaVars expr = execStateT (bindMetas_ go expr) mempty
  where
    go m = do
      visited <- get
      unless (m `HashSet.member` visited) $ do
        put $ HashSet.insert m visited
        bindMetas_ go $ metaType m
        sol <- solution m
        case sol of
          Left _ -> return ()
          Right e -> bindMetas_ go e

definitionMetaVars
  :: MonadIO m
  => Definition (Expr MetaVar) v
  -> m (HashSet MetaVar)
definitionMetaVars def = do
  x <- transverseDefinition (fmap Const . metaVars) def
  return $ getConst $ bitraverseDefinition Const (const $ Const mempty) x

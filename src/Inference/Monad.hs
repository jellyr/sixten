{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, TypeSynonymInstances #-}
module Inference.Monad where

import Control.Monad.Reader
import Data.Bifunctor
import Data.Foldable

import qualified Builtin.Names as Builtin
import Inference.MetaVar
import MonadContext
import Syntax
import qualified Syntax.Abstract as Abstract
import Util
import qualified Util.Tsil as Tsil
import Util.Tsil(Tsil)
import VIX
import TypedFreeVar

type FreeV = FreeVar (Abstract.Expr MetaVar)
type ConcreteM = Concrete.Expr FreeV
type AbstractM = Abstract.Expr Meta FreeV

type Polytype = AbstractM
type Rhotype = AbstractM -- No top-level foralls

newtype InstUntil = InstUntil Plicitness
  deriving (Eq, Ord, Show)

shouldInst :: Plicitness -> InstUntil -> Bool
shouldInst Explicit _ = False
shouldInst _ (InstUntil Explicit) = True
shouldInst p (InstUntil p') | p == p' = False
shouldInst _ _ = True

data InferEnv = InferEnv
  { localVariables :: Tsil Meta
  , inferLevel :: !Level
  }

type Infer = ReaderT InferEnv VIX

runInfer :: Infer a -> VIX a
runInfer i = runReaderT i InferEnv
  { localVariables = mempty
  , inferLevel = 1
  }

instance MonadContext Meta Infer where
  localVars = asks localVariables

  withVar v m = do
    locals <- localVars
    when (v `elem` toList locals) $ internalError "Duplicate var in context"

    local
      (\env -> env { localVariables = localVariables env `Tsil.Snoc` v })
      m

level :: Infer Level
level = asks inferLevel

enterLevel :: Infer a -> Infer a
enterLevel = local $ \e -> e { inferLevel = inferLevel e + 1 }

exists
  :: NameHint
  -> Plicitness
  -> Abstract.Expr (MetaVar Plicitness Abstract.Expr)
  -> Infer AbstractM
exists hint d typ = do
  locals <- toVector <$> asks localVariables
  let plocals = (\v -> (metaData v, v)) <$> locals
  tele <- metaTelescopeM plocals
  let abstr = teleAbstraction locals
  typ' <- Abstract.pis tele <$> abstractM abstr typ
  v <- existsAtLevel hint d typ' =<< level
  return $ Abstract.apps (pure v) $ second pure <$> plocals

existsType
  :: NameHint
  -> Infer AbstractM
existsType n = exists n Explicit Builtin.Type

existsVar
  :: NameHint
  -> Plicitness
  -> AbstractM
  -> Infer AbstractM
existsVar _ Constraint typ = return $ Builtin.UnsolvedConstraint typ
existsVar h Implicit typ = exists h Implicit typ
existsVar h Explicit typ = exists h Explicit typ

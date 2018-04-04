{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, TypeSynonymInstances #-}
module Inference.Monad where

import Control.Monad.Reader
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable

import qualified Builtin.Names as Builtin
import Inference.MetaVar
import MonadContext
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete.Scoped as Concrete
import TypedFreeVar
import Util
import qualified Util.Tsil as Tsil
import Util.Tsil(Tsil)
import VIX

type FreeV = FreeVar (Abstract.Expr MetaVar)
type ConcreteM = Concrete.Expr FreeV
type AbstractM = Abstract.Expr MetaVar FreeV

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
  { localVariables :: Tsil FreeV
  , inferLevel :: !Level
  }

type Infer = ReaderT InferEnv VIX

runInfer :: Infer a -> VIX a
runInfer i = runReaderT i InferEnv
  { localVariables = mempty
  , inferLevel = 1
  }

instance MonadContext FreeV Infer where
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
  -> Abstract.Expr MetaVar FreeV
  -> Infer AbstractM
exists hint d typ = do
  locals <- toVector <$> asks localVariables
  let plocals = (\v -> (Explicit, v)) <$> locals
      tele = varTelescope plocals
      abstr = teleAbstraction locals
      typ' = Abstract.pis tele $ abstract abstr typ
  typ'' <- traverse (error "exists not closed") typ'
  v <- existsAtLevel hint d typ'' =<< level
  return $ Abstract.Meta v $ pure <$> locals

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

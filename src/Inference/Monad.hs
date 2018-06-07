{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, OverloadedStrings, TypeSynonymInstances #-}
module Inference.Monad where

import Control.Monad.Except
import Control.Monad.Reader

import qualified Builtin.Names as Builtin
import Inference.MetaVar
import MonadContext
import MonadFresh
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete.Scoped as Concrete
import TypedFreeVar
import Util
import Util.Tsil(Tsil)
import VIX

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
  , inferTouchables :: !(MetaVar -> Bool)
  }

newtype Infer a = InferMonad (ReaderT InferEnv VIX a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadFix, MonadError Error, MonadFresh, MonadVIX)

runInfer :: Infer a -> VIX a
runInfer (InferMonad i) = runReaderT i InferEnv
  { localVariables = mempty
  , inferLevel = 1
  , inferTouchables = const True
  }

instance MonadContext FreeV Infer where
  localVars = InferMonad $ asks localVariables

  inUpdatedContext f (InferMonad m) = do
    InferMonad $ local
      (\env -> env { localVariables = f $ localVariables env })
      m

level :: Infer Level
level = InferMonad $ asks inferLevel

enterLevel :: Infer a -> Infer a
enterLevel (InferMonad m) = InferMonad $ local (\e -> e { inferLevel = inferLevel e + 1 }) m

exists
  :: NameHint
  -> Plicitness
  -> AbstractM
  -> Infer AbstractM
exists hint d typ = do
  locals <- toVector <$> localVars
  let tele = varTelescope locals
      abstr = teleAbstraction locals
      typ' = Abstract.pis tele $ abstract abstr typ
  logMeta 30 "exists typ" typ
  typ'' <- traverse (error "exists not closed") typ'
  v <- existsAtLevel hint d typ'' (teleLength tele) =<< level
  return $ Abstract.Meta v $ (\fv -> (varData fv, pure fv)) <$> locals

existsType
  :: NameHint
  -> Infer AbstractM
existsType n = exists n Explicit Builtin.Type

getTouchable :: Infer (MetaVar -> Bool)
getTouchable = InferMonad $ asks inferTouchables

untouchable :: Infer a -> Infer a
untouchable (InferMonad i) = do
  v <- fresh
  InferMonad $ local (\s -> s { inferTouchables = \m -> inferTouchables s m && metaId m > v }) i

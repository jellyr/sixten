{-# LANGUAGE DefaultSignatures, GADTs, MultiParamTypeClasses #-}
module MonadContext where

import Control.Monad.Trans

import Util.Tsil

class Monad m => MonadContext v m where
  withVar :: v -> m a -> m a
  localVars :: m (Tsil v)

  default localVars
    :: (MonadTrans t, MonadContext v m1, m ~ t m1)
    => m (Tsil v)
  localVars = lift localVars

withVars :: (MonadContext v m, Foldable t) => t v -> m a -> m a
withVars vs m = foldr withVar m vs

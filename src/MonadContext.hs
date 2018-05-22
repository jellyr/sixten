{-# LANGUAGE DefaultSignatures, FlexibleInstances, FunctionalDependencies, GADTs, MultiParamTypeClasses, UndecidableInstances #-}
module MonadContext where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Identity
import Control.Monad.Writer

import Util.Tsil

class Monad m => MonadContext v m | m -> v where
  withVar :: v -> m a -> m a
  localVars :: m (Tsil v)

  default localVars
    :: (MonadTrans t, MonadContext v m1, m ~ t m1)
    => m (Tsil v)
  localVars = lift localVars

withVars :: (MonadContext v m, Foldable t) => t v -> m a -> m a
withVars vs m = foldr withVar m vs

-------------------------------------------------------------------------------
-- mtl instances
-------------------------------------------------------------------------------
instance MonadContext v m => MonadContext v (ReaderT r m) where
  withVar v (ReaderT m) = ReaderT $ withVar v . m
instance (Monoid w, MonadContext v m) => MonadContext v (WriterT w m) where
  withVar v (WriterT m) = WriterT $ withVar v m
instance MonadContext v m => MonadContext v (StateT s m) where
  withVar v (StateT m) = StateT $ withVar v . m
instance MonadContext v m => MonadContext v (IdentityT m) where
  withVar v (IdentityT m) = IdentityT $ withVar v m

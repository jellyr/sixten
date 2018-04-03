{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, OverloadedStrings #-}
module Inference.MetaVar where

import Control.Monad.Except
import Control.Monad.ST
import Data.Bitraversable
import Data.Function
import Data.Hashable
import Data.Monoid
import Data.STRef
import Data.String
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Void

import Syntax.Abstract
import MonadFresh
import Syntax
import Util
import VIX

newtype Level = Level Int
  deriving (Eq, Num, Ord, Show)

instance Pretty Level where
  pretty (Level i) = pretty i

type MetaRef = STRef RealWorld (Either Level (Expr MetaVar Void))

data MetaVar = MetaVar
  { metaId  :: !Int
  , metaType :: Expr MetaVar Void
  , metaHint :: !NameHint
  , metaRef :: !MetaRef
  , metaPlicitness :: !Plicitness
  }

instance Eq MetaVar where
  (==) = (==) `on` metaId

instance Ord MetaVar where
  compare = compare `on` metaId

instance Hashable MetaVar where
  hashWithSalt s = hashWithSalt s . metaId

instance Show MetaVar where
  showsPrec d (MetaVar i t h _ _) = showParen (d > 10) $
    showString "Meta" . showChar ' ' . showsPrec 11 i .
    showChar ' ' . showsPrec 11 t . showChar ' ' . showsPrec 11 h .
    showChar ' ' . showString "<Ref>"

existsAtLevel
  :: (MonadVIX m, MonadIO m)
  => NameHint
  -> Plicitness
  -> Expr MetaVar Void
  -> Level
  -> m MetaVar 
existsAtLevel hint p typ l = do
  i <- fresh
  ref <- liftST $ newSTRef $ Left l
  logVerbose 20 $ "exists: " <> fromString (show i)
  return $ MetaVar i typ hint ref p

solution
  :: MonadIO m
  => MetaVar
  -> m (Either Level (Expr MetaVar Void))
solution = liftST . readSTRef . metaRef

solve
  :: MonadIO m
  => MetaVar
  -> Expr MetaVar Void
  -> m ()
solve m x = liftST $ writeSTRef (metaRef m) $ Right x

data WithVar a = WithVar !MetaVar a

instance Eq (WithVar a) where
  WithVar v1 _ == WithVar v2 _ = v1 == v2

instance Pretty a => Pretty (WithVar a) where
  prettyM (WithVar _ x) = prettyM x

prettyMetaVar
  :: MonadIO m
  => MetaVar
  -> m Doc
prettyMetaVar x = do
  let name = "?" <> fromNameHint "" fromName (metaHint x) <> shower (metaId x)
  esol <- solution x
  case esol of
    Left _ -> return name
    Right sol -> do
      sol' <- prettyMeta sol
      return $ PP.parens $ name PP.<+> "=" PP.<+> sol'

prettyMeta
  :: (Pretty v, MonadIO m)
  => Expr MetaVar v
  -> m Doc
prettyMeta e = do
  e' <- bitraverse (\m -> WithVar m <$> prettyMetaVar m) (pure . pretty) e
  return $ pretty e'

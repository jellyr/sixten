{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, OverloadedStrings #-}
module Inference.MetaVar where

import Control.Monad.Except
import Control.Monad.ST
import Control.Monad.State
import Data.Bifoldable
import Data.Bitraversable
import Data.Function
import Data.Hashable
import qualified Data.HashSet as HashSet
import Data.HashSet(HashSet)
import Data.Monoid
import Data.STRef
import Data.String
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Vector(Vector)
import Data.Void

import MonadFresh
import Syntax
import Syntax.Abstract
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

traverseMeta
  :: MonadIO m
  => (Expr MetaVar v -> m (Expr MetaVar v))
  -> MetaVar
  -> Vector (Plicitness, Expr MetaVar v)
  -> m (Expr MetaVar v)
traverseMeta f m es = do
  sol <- solution m
  case sol of
    Left _ -> return $ Meta m es
    Right e -> f $ apps (vacuous e) es

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

logMeta
  :: (MonadIO m, Pretty v, MonadVIX m)
  => Int
  -> String
  -> Expr MetaVar v
  -> m ()
logMeta v s e = whenVerbose v $ do
  i <- liftVIX $ gets vixIndent
  d <- prettyMeta e
  VIX.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> showWide d

zonk :: MonadIO m => Expr MetaVar v -> m (Expr MetaVar v)
zonk = bindMeta $ \m es -> do
  sol <- solution m
  case sol of
    Left _ -> return $ Meta m es
    Right e -> return $ apps (vacuous e) es

metaVars :: MonadIO m => Expr MetaVar v -> m (HashSet MetaVar)
metaVars expr = execStateT (bitraverse_ go (const $ pure ()) expr) mempty
  where
    go m = do
      visited <- get
      unless (m `HashSet.member` visited) $ do
        bitraverse_ go (const $ pure ()) $ metaType m
        sol <- solution m
        case sol of
          Left _ -> return ()
          Right e -> bitraverse_ go (const $ pure ()) e

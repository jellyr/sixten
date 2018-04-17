{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, OverloadedStrings #-}
module Inference.MetaVar where

import Control.Monad.Except
import Control.Monad.ST
import Control.Monad.State
import Data.Bitraversable
import Data.Function
import Data.Hashable
import Data.Monoid
import Data.STRef
import Data.String
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Vector(Vector)
import Data.Void

import MonadFresh
import Syntax
import Syntax.Abstract
import TypedFreeVar
import Util
import VIX

newtype Level = Level Int
  deriving (Eq, Num, Ord, Show)

instance Pretty Level where
  pretty (Level i) = pretty i

type MetaRef = STRef RealWorld (Either Level (Expr MetaVar Void))

type FreeV = FreeVar Plicitness (Expr MetaVar)

data MetaVar = MetaVar
  { metaId :: !Int
  , metaType :: Expr MetaVar Void
  , metaHint :: !NameHint
  , metaPlicitness :: !Plicitness
  , metaParams :: Telescope Plicitness (Expr MetaVar) Void
  , metaGeneraliser :: !FreeV
  , metaRef :: !MetaRef
  }

instance Eq MetaVar where
  (==) = (==) `on` metaId

instance Ord MetaVar where
  compare = compare `on` metaId

instance Hashable MetaVar where
  hashWithSalt s = hashWithSalt s . metaId

instance Show MetaVar where
  showsPrec d (MetaVar i t h p ps g _) = showParen (d > 10) $
    showString "Meta" . showChar ' ' .
    showsPrec 11 i . showChar ' ' .
    showsPrec 11 t . showChar ' ' .
    showsPrec 11 h . showChar ' ' .
    showsPrec 11 p . showChar ' ' .
    showsPrec 11 ps . showChar ' ' .
    showsPrec 11 g . showChar ' ' .
    showString "<Ref>"

existsAtLevel
  :: (MonadVIX m, MonadIO m)
  => NameHint
  -> Plicitness
  -> Telescope Plicitness (Expr MetaVar) Void
  -> Expr MetaVar Void
  -> FreeV
  -> Level
  -> m MetaVar
existsAtLevel hint p tele typ g l = do
  i <- fresh
  ref <- liftST $ newSTRef $ Left l
  logVerbose 20 $ "exists: " <> fromString (show i)
  return $ MetaVar i typ hint p tele g ref

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

generalise
  :: MonadIO m
  => MetaVar
  -> m ()
generalise m = do
  let tele = metaParams m
  solve m
    $ lams tele
    $ toScope $ pure $ B $ TeleVar $ teleLength tele - 1

traverseMetaSolution
  :: MonadIO m
  => (Expr MetaVar v -> m (Expr MetaVar v))
  -> MetaVar
  -> Vector (Plicitness, Expr MetaVar v)
  -> m (Expr MetaVar v)
traverseMetaSolution f m es = do
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

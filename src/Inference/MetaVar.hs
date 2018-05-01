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
import qualified Data.Vector as Vector
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
  , metaRef :: !MetaRef
  }

instance Eq MetaVar where
  (==) = (==) `on` metaId

instance Ord MetaVar where
  compare = compare `on` metaId

instance Hashable MetaVar where
  hashWithSalt s = hashWithSalt s . metaId

instance Show MetaVar where
  showsPrec d (MetaVar i t h p ps _) = showParen (d > 10) $
    showString "Meta" . showChar ' ' .
    showsPrec 11 i . showChar ' ' .
    showsPrec 11 t . showChar ' ' .
    showsPrec 11 h . showChar ' ' .
    showsPrec 11 p . showChar ' ' .
    showsPrec 11 ps . showChar ' ' .
    showString "<Ref>"

existsAtLevel
  :: (MonadVIX m, MonadIO m)
  => NameHint
  -> Plicitness
  -> Telescope Plicitness (Expr MetaVar) Void
  -> Expr MetaVar Void
  -> Level
  -> m MetaVar
existsAtLevel hint p tele typ l = do
  i <- fresh
  ref <- liftST $ newSTRef $ Left l
  logVerbose 20 $ "exists: " <> fromString (show i)
  return $ MetaVar i typ hint p tele ref

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

gatherDefMetas
  :: MonadFresh m
  => Vector FreeV
  -> Definition (Expr MetaVar) FreeV
  -> m (Definition (Expr MetaVar) FreeV)
gatherDefMetas outerVars def = case def of
  Definition a i e -> Definition a i <$> gatherExprMetas outerVars e
  DataDefinition d t -> uncurry DataDefinition <$> gatherDataDefMetas outerVars d t

gatherDataDefMetas
  :: MonadFresh m
  => Vector FreeV
  -> DataDef (Expr MetaVar) FreeV
  -> Expr MetaVar FreeV
  -> m (DataDef (Expr MetaVar) FreeV, Expr MetaVar FreeV)
gatherDataDefMetas outerVars (DataDef cs) typ = do
  typ' <- gatherExprMetas outerVars typ

  vs <- forTeleWithPrefixM (telescope typ') $ \h p s vs -> do
    let t = instantiateTele pure vs s
    freeVar h p t

  let abstr = teleAbstraction vs

  cs' <- forM cs $ \(ConstrDef c s) -> do
    e <- gatherExprMetas outerVars $ instantiateTele pure vs s
    return $ ConstrDef c $ abstract abstr e

  return (DataDef cs', typ')

gatherExprMetas
  :: MonadFresh m
  => Vector FreeV
  -> Expr MetaVar FreeV
  -> m (Expr MetaVar FreeV)
gatherExprMetas outerVars expr = case expr of
  Var _ -> return expr
  Meta m vs -> undefined
  Global _ -> return expr
  Con _ -> return expr
  Lit _ -> return expr
  Pi h p t s -> do
    t' <- gatherExprMetas outerVars t
    v <- freeVar h p t'
    let e = instantiate1 (pure v) s
    e' <- gatherExprMetas outerVars e
    let s' = abstract1 v e'
    return $ Pi h p t' s'
  Lam h p t s -> do
    t' <- gatherExprMetas outerVars t
    v <- freeVar h p t'
    let e = instantiate1 (pure v) s
    e' <- gatherExprMetas outerVars e
    let s' = abstract1 v e'
    return $ Pi h p t' s'
  App e1 p e2 -> App <$> gatherExprMetas outerVars e1 <*> pure p <*> gatherExprMetas outerVars e2
  Let ds scope -> do
    vs <- forMLet ds $ \h _ t -> do
      t' <- gatherExprMetas outerVars t
      freeVar h Explicit t'
    let abstr = letAbstraction vs
    ds' <- iforMLet ds $ \i h s _ -> do
      let e = instantiateLet pure vs s
      e' <- gatherExprMetas outerVars e
      let v = vs Vector.! i
          s' = abstract abstr e'
      return $ LetBinding h s' $ varType v
    let e = instantiateLet pure vs scope
    e' <- gatherExprMetas outerVars e
    let scope' = abstract abstr e'
    return $ Let (LetRec ds') scope'
  Case e brs t -> Case <$> gatherExprMetas outerVars e <*> gatherBranchMetas outerVars brs <*> gatherExprMetas outerVars t
  ExternCode e t -> ExternCode <$> mapM (gatherExprMetas outerVars) e <*> gatherExprMetas outerVars t

gatherBranchMetas
  :: MonadFresh m
  => Vector FreeV
  -> Branches Plicitness (Expr MetaVar) FreeV
  -> m (Branches Plicitness (Expr MetaVar) FreeV)
gatherBranchMetas outerVars brs = case brs of
  ConBranches cbrs -> _
  LitBranches lbrs def -> _

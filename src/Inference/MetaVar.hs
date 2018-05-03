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

type FreeBindVar meta = FreeVar Plicitness (Expr meta)

-- TODO move?
bindDefMetasF
  :: MonadFresh m
  => (meta -> Vector (Plicitness, Expr meta (FreeBindVar meta)) -> m (Expr meta' (FreeBindVar meta)))
  -> Definition (Expr meta) (FreeBindVar meta)
  -> m (Definition (Expr meta') (FreeBindVar meta))
bindDefMetasF f def = case def of
  Definition a i e -> Definition a i <$> bindMetasF f e
  DataDefinition d t -> uncurry DataDefinition <$> bindDataDefMetasF f d t

bindDataDefMetasF
  :: MonadFresh m
  => (meta -> Vector (Plicitness, Expr meta (FreeBindVar meta)) -> m (Expr meta' (FreeBindVar meta)))
  -> DataDef (Expr meta) (FreeBindVar meta)
  -> Expr meta (FreeBindVar meta)
  -> m (DataDef (Expr meta') (FreeBindVar meta), Expr meta' (FreeBindVar meta))
bindDataDefMetasF f (DataDef cs) typ = do
  vs <- forTeleWithPrefixM (telescope typ) $ \h p s vs -> do
    let t = instantiateTele pure vs s
    freeVar h p t

  let abstr = teleAbstraction vs

  cs' <- forM cs $ \(ConstrDef c s) -> do
    e <- bindMetasF f $ instantiateTele pure vs s
    return $ ConstrDef c $ abstract abstr e

  typ' <- bindMetasF f typ

  return (DataDef cs', typ')

bindMetasF
  :: MonadFresh m
  => (meta -> Vector (Plicitness, Expr meta (FreeBindVar meta)) -> m (Expr meta' (FreeBindVar meta)))
  -> Expr meta (FreeBindVar meta)
  -> m (Expr meta' (FreeBindVar meta))
bindMetasF f expr = case expr of
  Var v -> return $ Var v
  Meta m vs -> f m vs
  Global g -> return $ Global g
  Con c -> return $ Con c
  Lit l -> return $ Lit l
  Pi h p t s -> do
    v <- freeVar h p t
    t' <- bindMetasF f t
    let e = instantiate1 (pure v) s
    e' <- bindMetasF f e
    let s' = abstract1 v e'
    return $ Pi h p t' s'
  Lam h p t s -> do
    v <- freeVar h p t
    t' <- bindMetasF f t
    let e = instantiate1 (pure v) s
    e' <- bindMetasF f e
    let s' = abstract1 v e'
    return $ Pi h p t' s'
  App e1 p e2 -> App <$> bindMetasF f e1 <*> pure p <*> bindMetasF f e2
  Let ds scope -> do
    vs <- forMLet ds $ \h _ t -> freeVar h Explicit t
    let abstr = letAbstraction vs
    ds' <- forMLet ds $ \h s t -> do
      t' <- bindMetasF f t
      let e = instantiateLet pure vs s
      e' <- bindMetasF f e
      let s' = abstract abstr e'
      return $ LetBinding h s' t'
    let e = instantiateLet pure vs scope
    e' <- bindMetasF f e
    let scope' = abstract abstr e'
    return $ Let (LetRec ds') scope'
  Case e brs t -> Case <$> bindMetasF f e <*> gatherBranchMetas f brs <*> bindMetasF f t
  ExternCode e t -> ExternCode <$> mapM (bindMetasF f) e <*> bindMetasF f t

gatherBranchMetas
  :: MonadFresh m
  => (meta -> Vector (Plicitness, Expr meta (FreeBindVar meta)) -> m (Expr meta' (FreeBindVar meta)))
  -> Branches Plicitness (Expr meta) (FreeBindVar meta)
  -> m (Branches Plicitness (Expr meta') (FreeBindVar meta))
gatherBranchMetas f brs = case brs of
  ConBranches cbrs -> ConBranches <$> do
    forM cbrs $ \(ConBranch c tele scope) -> do
      vs <- forTeleWithPrefixM tele $ \h p s vs -> do
        let t = instantiateTele pure vs s
        freeVar h p t

      let abstr = teleAbstraction vs
          expr = instantiateTele pure vs scope

      expr' <- bindMetasF f expr
      let scope' = abstract abstr expr'

      tele' <- forMTele tele $ \h p s -> do
        let e = instantiateTele pure vs s
        e' <- bindMetasF f e
        let s' = abstract abstr e'
        return $ TeleArg h p s'

      return $ ConBranch c (Telescope tele') scope'
  LitBranches lbrs def ->
    LitBranches
      <$> mapM (\(LitBranch l br) -> LitBranch l <$> bindMetasF f br) lbrs
      <*> bindMetasF f def

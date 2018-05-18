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

import MonadContext
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
  , metaRef :: !MetaRef
  }

instance Eq MetaVar where
  (==) = (==) `on` metaId

instance Ord MetaVar where
  compare = compare `on` metaId

instance Hashable MetaVar where
  hashWithSalt s = hashWithSalt s . metaId

instance Show MetaVar where
  showsPrec d (MetaVar i t h p _) = showParen (d > 10) $
    showString "Meta" . showChar ' ' .
    showsPrec 11 i . showChar ' ' .
    showsPrec 11 t . showChar ' ' .
    showsPrec 11 h . showChar ' ' .
    showsPrec 11 p . showChar ' ' .
    showString "<Ref>"

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
  return $ MetaVar i typ hint p ref

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
bindDefMetas
  :: (MonadFresh m, MonadContext (FreeBindVar meta') m)
  => (meta -> Vector (Plicitness, Expr meta (FreeBindVar meta')) -> m (Expr meta' (FreeBindVar meta')))
  -> Definition (Expr meta) (FreeBindVar meta')
  -> m (Definition (Expr meta') (FreeBindVar meta'))
bindDefMetas f def = case def of
  Definition a i e -> Definition a i <$> bindMetas f e
  DataDefinition d t -> uncurry DataDefinition <$> bindDataDefMetas f d t

bindDefMetas'
  :: (MonadFresh m, MonadContext (FreeBindVar meta') m)
  => (meta -> Vector (Plicitness, Expr meta' (FreeBindVar meta')) -> m (Expr meta' (FreeBindVar meta')))
  -> Definition (Expr meta) (FreeBindVar meta')
  -> m (Definition (Expr meta') (FreeBindVar meta'))
bindDefMetas' f = bindDefMetas $ \m es -> do
  es' <- forM es $ \(p, e) -> do
    e' <- bindMetas' f e
    return (p, e')
  f m es'

bindDataDefMetas
  :: (MonadFresh m, MonadContext (FreeBindVar meta') m)
  => (meta -> Vector (Plicitness, Expr meta (FreeBindVar meta')) -> m (Expr meta' (FreeBindVar meta')))
  -> DataDef (Expr meta) (FreeBindVar meta')
  -> Expr meta (FreeBindVar meta')
  -> m (DataDef (Expr meta') (FreeBindVar meta'), Expr meta' (FreeBindVar meta'))
bindDataDefMetas f (DataDef cs) typ = do
  vs <- forTeleWithPrefixM (telescope typ) $ \h p s vs -> do
    let t = instantiateTele pure vs s
    -- TODO inefficient: make special-case forTeleWithPrefix + withVars
    t' <- withVars vs $ bindMetas f t
    freeVar h p t'

  withVars vs $ do

    let abstr = teleAbstraction vs

    cs' <- forM cs $ \(ConstrDef c s) -> do
      e <- bindMetas f $ instantiateTele pure vs s
      return $ ConstrDef c $ abstract abstr e

    typ' <- bindMetas f typ

    return (DataDef cs', typ')

bindMetas
  :: (MonadFresh m, MonadContext (FreeBindVar meta') m)
  => (meta -> Vector (Plicitness, Expr meta (FreeBindVar meta')) -> m (Expr meta' (FreeBindVar meta')))
  -> Expr meta (FreeBindVar meta')
  -> m (Expr meta' (FreeBindVar meta'))
bindMetas f expr = case expr of
  Var v -> return $ Var v
  Meta m es -> f m es
  Global g -> return $ Global g
  Con c -> return $ Con c
  Lit l -> return $ Lit l
  Pi h p t s -> do
    t' <- bindMetas f t
    v <- freeVar h p t'
    let e = instantiate1 (pure v) s
    e' <- bindMetas f e
    let s' = abstract1 v e'
    return $ Pi h p t' s'
  Lam h p t s -> do
    t' <- bindMetas f t
    v <- freeVar h p t'
    let e = instantiate1 (pure v) s
    e' <- bindMetas f e
    let s' = abstract1 v e'
    return $ Pi h p t' s'
  App e1 p e2 -> App <$> bindMetas f e1 <*> pure p <*> bindMetas f e2
  Let ds scope -> do
    vs <- forMLet ds $ \h _ t -> do
      t' <- bindMetas f t
      freeVar h Explicit t'
    let abstr = letAbstraction vs
    withVars vs $ do
      ds' <- iforMLet ds $ \i h s t -> do
        let e = instantiateLet pure vs s
        e' <- bindMetas f e
        let s' = abstract abstr e'
            t' = varType $ vs Vector.! i
        return $ LetBinding h s' t'
      let e = instantiateLet pure vs scope
      e' <- bindMetas f e
      let scope' = abstract abstr e'
      return $ Let (LetRec ds') scope'
  Case e brs t -> Case <$> bindMetas f e <*> bindBranchMetas f brs <*> bindMetas f t
  ExternCode e t -> ExternCode <$> mapM (bindMetas f) e <*> bindMetas f t

bindMetas'
  :: (MonadFresh m, MonadContext (FreeBindVar meta') m)
  => (meta -> Vector (Plicitness, Expr meta' (FreeBindVar meta')) -> m (Expr meta' (FreeBindVar meta')))
  -> Expr meta (FreeBindVar meta')
  -> m (Expr meta' (FreeBindVar meta'))
bindMetas' f = bindMetas $ \m es -> do
  es' <- forM es $ \(p, e) -> do
    e' <- bindMetas' f e
    return (p, e')
  f m es'

bindBranchMetas
  :: (MonadFresh m, MonadContext (FreeBindVar meta') m)
  => (meta -> Vector (Plicitness, Expr meta (FreeBindVar meta')) -> m (Expr meta' (FreeBindVar meta')))
  -> Branches Plicitness (Expr meta) (FreeBindVar meta')
  -> m (Branches Plicitness (Expr meta') (FreeBindVar meta'))
bindBranchMetas f brs = case brs of
  ConBranches cbrs -> ConBranches <$> do
    forM cbrs $ \(ConBranch c tele scope) -> do
      vs <- forTeleWithPrefixM tele $ \h p s vs -> do
        let t = instantiateTele pure vs s
        -- TODO inefficient: make special-case forTeleWithPrefix + withVars
        t' <- withVars vs $ bindMetas f t
        freeVar h p t'

      let abstr = teleAbstraction vs
          expr = instantiateTele pure vs scope

      expr' <- withVars vs $ bindMetas f expr
      let tele' = varTelescope vs
          scope' = abstract abstr expr'

      return $ ConBranch c tele' scope'
  LitBranches lbrs def ->
    LitBranches
      <$> mapM (\(LitBranch l br) -> LitBranch l <$> bindMetas f br) lbrs
      <*> bindMetas f def

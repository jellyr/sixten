{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, OverloadedStrings #-}
module Inference.MetaVar where

import Control.Monad.Except
import Control.Monad.ST
import Control.Monad.State
import Data.Bitraversable
import Data.Either
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
  , metaArity :: !Int
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
  showsPrec d (MetaVar i t a h p _) = showParen (d > 10) $
    showString "MetaVar" . showChar ' ' .
    showsPrec 11 i . showChar ' ' .
    showsPrec 11 t . showChar ' ' .
    showsPrec 11 a . showChar ' ' .
    showsPrec 11 h . showChar ' ' .
    showsPrec 11 p . showChar ' ' .
    showString "<Ref>"

existsAtLevel
  :: (MonadVIX m, MonadIO m)
  => NameHint
  -> Plicitness
  -> Expr MetaVar Void
  -> Int
  -> Level
  -> m MetaVar
existsAtLevel hint p typ a l = do
  i <- fresh
  ref <- liftST $ newSTRef $ Left l
  logVerbose 20 $ "exists: " <> shower i
  logMeta 20 "exists typ: " typ
  return $ MetaVar i typ a hint p ref

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

isSolved :: MonadIO m => MetaVar -> m Bool
isSolved = fmap isRight . solution

isUnsolved :: MonadIO m => MetaVar -> m Bool
isUnsolved = fmap isLeft . solution

-- | Like freeVar, but with logging and explicitisation
forall
  :: (MonadFresh m, MonadVIX m, MonadIO m)
  => NameHint
  -> Plicitness
  -> e (FreeVar Plicitness e)
  -> m (FreeVar Plicitness e)
forall h p t = do
  v <- freeVar h (explicitise p) t
  logVerbose 20 $ "forall: " <> shower (varId v)
  return v

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
  :: (MonadIO m, MonadVIX m)
  => MetaVar
  -> m Doc
prettyMetaVar x = do
  let name = "?" <> fromNameHint "" fromName (metaHint x) <> shower (metaId x) <> "[" <> shower (metaArity x) <> "]"
  esol <- solution x
  case esol of
    Left _ -> return name
    Right sol -> do
      v <- liftVIX $ gets vixVerbosity
      sol' <- prettyMeta sol
      if v <= 30 then
        return $ PP.parens $ sol'
      else
        return $ PP.parens $ name PP.<+> "=" PP.<+> sol'

prettyMeta
  :: (Pretty v, MonadIO m, MonadVIX m)
  => Expr MetaVar v
  -> m Doc
prettyMeta e = do
  e' <- bitraverse (\m -> WithVar m <$> prettyMetaVar m) (pure . pretty) e
  return $ pretty e'

prettyDefMeta
  :: (Pretty v, MonadIO m, MonadVIX m)
  => Definition (Expr MetaVar) v
  -> m Doc
prettyDefMeta e = do
  e' <- bitraverseDefinition (\m -> WithVar m <$> prettyMetaVar m) (pure . pretty) e
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

logDefMeta
  :: (MonadIO m, Pretty v, MonadVIX m)
  => Int
  -> String
  -> Definition (Expr MetaVar) v
  -> m ()
logDefMeta v s e = whenVerbose v $ do
  i <- liftVIX $ gets vixIndent
  d <- prettyDefMeta e
  VIX.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> showWide d

type FreeBindVar meta = FreeVar Plicitness (Expr meta)

instantiatedMetaType
  :: (MonadError Error m, MonadFresh m, MonadVIX m, MonadIO m)
  => MetaVar
  -> m (Vector FreeV, Expr MetaVar (FreeBindVar MetaVar))
instantiatedMetaType m = go mempty (metaArity m) (vacuous $ metaType m)
  where
    go vs 0 t = return (toVector $ reverse vs, t)
    go vs n (Pi h a t s) = do
      v <- forall h a t
      go (v:vs) (n - 1) (instantiate1 (pure v) s)
    go _ _ _ = internalError "instantiatedMetaType"

-- TODO move?
bindDefMetas
  :: (MonadFresh m, MonadContext (FreeBindVar meta') m, MonadVIX m, MonadIO m)
  => (meta -> Vector (Plicitness, Expr meta (FreeBindVar meta')) -> m (Expr meta' (FreeBindVar meta')))
  -> Definition (Expr meta) (FreeBindVar meta')
  -> Expr meta (FreeBindVar meta')
  -> m (Definition (Expr meta') (FreeBindVar meta'), Expr meta' (FreeBindVar meta'))
bindDefMetas f def typ = case def of
  Definition a i e -> (,) <$> (Definition a i <$> bindMetas f e) <*> bindMetas f typ
  DataDefinition d rep -> do
    (d', typ') <- bindDataDefMetas f d typ
    rep' <- bindMetas f rep
    return (DataDefinition d' rep', typ')

bindDefMetas'
  :: (MonadFresh m, MonadContext (FreeBindVar meta') m, MonadVIX m, MonadIO m)
  => (meta -> Vector (Plicitness, Expr meta' (FreeBindVar meta')) -> m (Expr meta' (FreeBindVar meta')))
  -> Definition (Expr meta) (FreeBindVar meta')
  -> Expr meta (FreeBindVar meta')
  -> m (Definition (Expr meta') (FreeBindVar meta'), Expr meta' (FreeBindVar meta'))
bindDefMetas' f = bindDefMetas $ \m es -> do
  es' <- traverse (traverse $ bindMetas' f) es
  f m es'

bindDataDefMetas
  :: (MonadFresh m, MonadContext (FreeBindVar meta') m, MonadVIX m, MonadIO m)
  => (meta -> Vector (Plicitness, Expr meta (FreeBindVar meta')) -> m (Expr meta' (FreeBindVar meta')))
  -> DataDef (Expr meta) (FreeBindVar meta')
  -> Expr meta (FreeBindVar meta')
  -> m (DataDef (Expr meta') (FreeBindVar meta'), Expr meta' (FreeBindVar meta'))
bindDataDefMetas f (DataDef cs) typ = do
  typ' <- bindMetas f typ

  vs <- forTeleWithPrefixM (telescope typ') $ \h p s vs -> do
    let t = instantiateTele pure vs s
    forall h p t

  withVars vs $ do

    let abstr = teleAbstraction vs

    cs' <- forM cs $ \(ConstrDef c s) -> do
      e <- bindMetas f $ instantiateTele pure vs s
      return $ ConstrDef c $ abstract abstr e

    return (DataDef cs', typ')

bindMetas
  :: (MonadFresh m, MonadContext (FreeBindVar meta') m, MonadVIX m, MonadIO m)
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
    v <- forall h p t'
    let e = instantiate1 (pure v) s
    e' <- bindMetas f e
    let s' = abstract1 v e'
    return $ Pi h p t' s'
  Lam h p t s -> do
    t' <- bindMetas f t
    v <- forall h p t'
    let e = instantiate1 (pure v) s
    e' <- bindMetas f e
    let s' = abstract1 v e'
    return $ Lam h p t' s'
  App e1 p e2 -> App <$> bindMetas f e1 <*> pure p <*> bindMetas f e2
  Let ds scope -> do
    vs <- forMLet ds $ \h _ t -> do
      t' <- bindMetas f t
      forall h Explicit t'
    let abstr = letAbstraction vs
    withVars vs $ do
      ds' <- iforMLet ds $ \i h s _ -> do
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
  :: (MonadFresh m, MonadContext (FreeBindVar meta') m, MonadVIX m, MonadIO m)
  => (meta -> Vector (Plicitness, Expr meta' (FreeBindVar meta')) -> m (Expr meta' (FreeBindVar meta')))
  -> Expr meta (FreeBindVar meta')
  -> m (Expr meta' (FreeBindVar meta'))
bindMetas' f = bindMetas $ \m es -> do
  es' <- traverse (traverse $ bindMetas' f) es
  f m es'

bindBranchMetas
  :: (MonadFresh m, MonadContext (FreeBindVar meta') m, MonadVIX m, MonadIO m)
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
        forall h p t'

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

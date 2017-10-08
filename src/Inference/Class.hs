{-# LANGUAGE FlexibleContexts, OverloadedStrings, PatternSynonyms, ViewPatterns #-}
module Inference.Class where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor
import qualified Data.HashMap.Lazy as HashMap
import Data.HashMap.Lazy(HashMap)
import Data.Maybe
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import qualified Builtin.Names as Builtin
import Inference.Monad
import Inference.Subtype
import Meta
import Syntax
import Syntax.Abstract
import Util
import VIX

pattern UnsolvedConstraint :: Expr v -> Expr v
pattern UnsolvedConstraint typ = App (Global Builtin.UnsolvedConstraintName) Explicit typ

existsVar
  :: (MonadVIX m, MonadIO m)
  => NameHint
  -> Plicitness
  -> AbstractM
  -> m AbstractM
existsVar _ Constraint typ = return $ UnsolvedConstraint typ
existsVar h Implicit typ = pure <$> exists h Implicit typ
existsVar h Explicit typ = pure <$> exists h Explicit typ

isConstraintVar :: MetaA -> Bool
isConstraintVar v = case metaData v of
  Constraint -> True
  Implicit -> False
  Explicit -> False

withVar
  :: MetaA
  -> Infer a
  -> Infer a
withVar v
  | isConstraintVar v = local $ \env ->
    env { constraints = (pure v, metaType v) : constraints env }
  | otherwise = id

withVars
  :: Vector MetaA
  -> Infer a
  -> Infer a
withVars xs b = foldr withVar b xs

elabUnsolvedConstraint
  :: Exists Plicitness Expr
  -> MetaA
  -> Infer AbstractM
elabUnsolvedConstraint ref var = do
  let typ = metaType var
  case typ of
    (appsView -> (Global className, _)) -> do
      -- Replace existentials in typ with universals
      (uniType, uniVarMap) <- universalise typ
      -- Try subsumption on all instances of the class until a match is found
      mclassInstances <- gets $ HashMap.lookup className . vixClassInstances
      case mclassInstances of
        Nothing -> throwLocated $ "Not a class: " <> pretty className
        Just globalClassInstances -> do
          localInstances <- asks constraints
          let candidates = [(Global g, vacuous t) | (g, t) <- globalClassInstances]
                <> localInstances
          matchingInstances <- forM candidates $ \(inst, instType) -> tryMaybe $ do
            f <- subtype instType uniType
            f inst
          case catMaybes matchingInstances of
            [] -> return $ pure var
            _:_:_ -> throwLocated $ "Ambiguous instance for " <> pretty className -- TODO error message
            [matchingInstance] -> do
              -- Elaborate any constraints introduced by the matching instance
              elabInstance <- elabExpr matchingInstance
              -- Replace the universals from before with the original existentials
              result <- deuniversalise uniVarMap elabInstance
              solve ref result
              return result
    _ -> throwLocated "Malformed constraint" -- TODO error message

-- | Replace existentials in typ with universals and return the mapping from
-- the new variables to the old existentials.
universalise :: AbstractM -> Infer (AbstractM, HashMap MetaA MetaA)
universalise typ = second snd <$> runStateT (bindM go typ) mempty
  where
    go v@MetaVar { metaRef = Just _ } = do
      (ltr, rtl) <- get
      case HashMap.lookup v ltr of
        Nothing -> do
          v' <- lift $ forall (metaHint v) (metaData v) (metaType v)
          put (HashMap.insert v v' ltr, HashMap.insert v' v rtl)
          return $ pure v'
        Just v' -> return $ pure v'
    go v = return $ pure v

deuniversalise :: HashMap MetaA MetaA -> AbstractM -> Infer AbstractM
deuniversalise rtl = bindM go
  where
    go v = return $ pure $ fromMaybe v $ HashMap.lookup v rtl

elabVar
  :: MetaA
  -> Infer AbstractM
elabVar var@MetaVar { metaRef = Just ref } = do
  sol <- solution ref
  case (sol, metaData var) of
    (Left _, Constraint) -> elabUnsolvedConstraint ref var
    (Left _, Implicit) -> return $ pure var
    (Left _, Explicit) -> return $ pure var
    (Right expr, _) -> elabExpr expr
elabVar var = return $ pure var

elabExpr
  :: AbstractM
  -> Infer AbstractM
elabExpr expr = do
  logMeta 30 "elabExpr expr" expr
  modifyIndent succ
  result <- case expr of
    UnsolvedConstraint typ -> do
      v <- exists mempty Constraint typ -- TODO maybe we don't need the var here?
      elabVar v
    Var v -> elabVar v
    Global g -> return $ Global g
    Con c -> return $ Con c
    Lit l -> return $ Lit l
    Pi h p t s -> absCase Pi h p t s
    Lam h p t s -> absCase Lam h p t s
    App e1 p e2 -> App <$> elabExpr e1 <*> pure p <*> elabExpr e2
    Let ds scope -> elabLet ds scope
    Case e brs t -> Case <$> elabExpr e <*> elabBranches brs <*> elabExpr t
    ExternCode ext t -> ExternCode <$> mapM elabExpr ext <*> elabExpr t
  modifyIndent pred
  logMeta 30 "elabExpr result" result
  return result
  where
    absCase c h p t s = do
      t' <- elabExpr t
      v <- forall h p t'
      let e = instantiate1 (pure v) s
      e' <- enterLevel $ withVar v $ elabExpr e
      s' <- abstract1M v e'
      return $ c h p t' s'

elabLet
  :: LetRec Expr MetaA
  -> Scope LetVar Expr MetaA
  -> Infer (Expr MetaA)
elabLet ds scope = do
  vs <- forMLet ds $ \h _ t -> do
    t' <- elabExpr t
    forall h Explicit t'
  let abstr = letAbstraction vs
  ds' <- iforMLet ds $ \i h s _ -> do
    let e = instantiateLet pure vs s
    e' <- elabExpr e
    s' <- abstractM abstr e'
    return $ LetBinding h s' $ metaType $ vs Vector.! i
  let expr = instantiateLet pure vs scope
  expr' <- elabExpr expr
  scope' <- abstractM abstr expr'
  return $ Let (LetRec ds') scope'

elabBranches
  :: Branches QConstr Plicitness Expr MetaA
  -> Infer (Branches QConstr Plicitness Expr MetaA)
elabBranches (ConBranches cbrs) = do
  cbrs' <- forM cbrs $ \(ConBranch qc tele brScope) -> do
    vs <- forTeleWithPrefixM tele $ \h p s vs -> do
      let t = instantiateTele pure vs s
      t' <- withVars vs $ elabExpr t -- TODO: This is a bit inefficient
      forall h p t'
    let brExpr = instantiateTele pure vs brScope
    brExpr' <- withVars vs $ elabExpr brExpr
    let abstr = teleAbstraction vs
    tele' <- Telescope
      <$> mapM (\v -> TeleArg (metaHint v) (metaData v) <$> abstractM abstr (metaType v)) vs
    brScope' <- abstractM abstr brExpr'
    return $ ConBranch qc tele' brScope'
  return $ ConBranches cbrs'
elabBranches (LitBranches lbrs def) = LitBranches
  <$> mapM (\(LitBranch l br) -> LitBranch l <$> elabExpr br) lbrs
  <*> elabExpr def

elabDef
  :: Definition Expr MetaA
  -> AbstractM
  -> Infer (Definition Expr MetaA)
elabDef (Definition i a e) _
  = Definition i a <$> elabExpr e
elabDef (DataDefinition (DataDef constrs) rep) typ = do
  typ' <- zonk typ
  let params = telescope typ'
  vs <- forTeleWithPrefixM params $ \h p s vs -> do
    let t = instantiateTele pure vs s
    forall h p t

  let abstr = teleAbstraction vs
  constrs' <- withVars vs $ forM constrs $ \constr -> forM constr $ \s -> do
    let e = instantiateTele pure vs s
    e' <- elabExpr e
    abstractM abstr e'

  rep' <- elabExpr rep
  return $ DataDefinition (DataDef constrs') rep'

elabRecursiveDefs
  :: Vector (sourceLoc, (MetaA, Definition Expr MetaA, AbstractM))
  -> Infer (Vector (sourceLoc, (MetaA, Definition Expr MetaA, AbstractM)))
elabRecursiveDefs defs = enterLevel $ do
  let localInstances
        = flip Vector.mapMaybe defs
        $ \(_, (v, def, _)) -> case def of
          DataDefinition {} -> Nothing
          Definition _ IsOrdinaryDefinition _ -> Nothing
          Definition _ IsInstance _ -> Just v { metaData = Constraint }
  withVars localInstances $ forM defs $ \(loc, (v, def, typ)) -> do
    typ' <- elabExpr typ
    def' <- elabDef def typ'
    return (loc, (v, def', typ'))
{-# LANGUAGE FlexibleContexts, OverloadedStrings, ViewPatterns #-}
module Inference.Constraint where

import Control.Monad.Except
import Control.Monad.State
import Data.Bifunctor
import Data.Foldable
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet(HashSet)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.Vector(Vector)
import Data.Void

import Analysis.Simplify
import Inference.MetaVar
import Inference.MetaVar.Zonk
import Inference.Monad
import qualified Inference.Normalise as Normalise
import Inference.Subtype
import MonadContext
import Syntax
import Syntax.Abstract
import TypedFreeVar
import Util
import VIX

elabMetaVar
  :: MetaVar
  -> Infer (Maybe (Expr MetaVar Void))
elabMetaVar m = do
  sol <- solution m
  case (sol, metaPlicitness m) of
    (Left _, Constraint) -> elabUnsolvedConstraint m
    (Left _, _) -> return Nothing
    (Right e, _) -> return $ Just e

elabUnsolvedConstraint
  :: MetaVar
  -> Infer (Maybe (Expr MetaVar Void))
elabUnsolvedConstraint m = do
  (vs, typ) <- instantiatedMetaType m
  case typ of
    (appsView -> (Global className, _)) -> do
      -- Try subsumption on all instances of the class until a match is found
      globalClassInstances <- liftVIX $ gets $ HashMap.lookupDefault mempty className . vixClassInstances
      let candidates = [(Global g, bimap absurd absurd t) | (g, t) <- globalClassInstances]
            <> [(pure v, varType v) | v <- toList vs, varData v == Constraint]
      matchingInstances <- forM candidates $ \(inst, instType) -> tryMaybe $ do
        f <- untouchable $ subtype instType typ
        f inst
      case catMaybes matchingInstances of
        [] -> do
          logVerbose 25 "No matching instance"
          return Nothing
        matchingInstance:_ -> do
          let sol = assertClosed $ lams (varTelescope vs) (abstract (teleAbstraction vs) matchingInstance)
          solve m sol
          logMeta 25 "Matching instance" matchingInstance
          logMeta 25 "Matching instance typ" typ
          return $ Just sol
    _ -> throwLocated "Malformed constraint" -- TODO error message
  where
    assertClosed :: Functor f => f FreeV -> f Void
    assertClosed = fmap $ error "elabMetaVar assertClosed"

elabExpr
  :: AbstractM
  -> Infer AbstractM
elabExpr = bindMetas $ \m es -> do
  sol <- elabMetaVar m
  case sol of
    Nothing -> Meta m <$> traverse (traverse elabExpr) es
    Just e -> elabExpr $ betaApps (vacuous e) es

elabDef
  :: Definition (Expr MetaVar) FreeV
  -> AbstractM
  -> Infer (Definition (Expr MetaVar) FreeV)
elabDef (Definition i a e) _
  = Definition i a <$> elabExpr e
elabDef (DataDefinition (DataDef constrs) rep) typ = do
  -- TODO should parameter telescope be built into DataDefinition?
  typ' <- zonk typ
  let params = telescope typ'
  vs <- forTeleWithPrefixM params $ \h p s vs -> do
    let t = instantiateTele pure vs s
    forall h p t

  let abstr = teleAbstraction vs
  constrs' <- withVars vs $ forM constrs $ \constr -> forM constr $ \s -> do
    let e = instantiateTele pure vs s
    e' <- elabExpr e
    return $ abstract abstr e'

  rep' <- elabExpr rep
  return $ DataDefinition (DataDef constrs') rep'

elabRecursiveDefs
  :: Vector (FreeV, Definition (Expr MetaVar) FreeV, AbstractM)
  -> Infer (Vector (FreeV, Definition (Expr MetaVar) FreeV, AbstractM))
elabRecursiveDefs defs
  = enterLevel
  $ forM defs $ \(v, def, typ) -> do
    typ' <- elabExpr typ
    def' <- elabDef def typ'
    return (v, def', typ')

mkConstraintVar :: AbstractM -> Infer AbstractM
mkConstraintVar = exists mempty Constraint

mergeConstraintVars
  :: HashSet MetaVar
  -> Infer (HashSet MetaVar) -- ^ The metavars that are still unsolved
mergeConstraintVars vars = do
  logShow 35 "mergeConstraintVars" vars
  _ <- foldlM go mempty vars
  vars' <- filterMSet isUnsolved vars
  logShow 35 "mergeConstraintVars result" vars'
  return vars'
  where
    go varTypes m@MetaVar { metaPlicitness = Constraint } = do
      let arity = metaArity m
      sol <- solution m
      case sol of
        Right _ -> return varTypes
        Left l -> do
          typ <- zonk $ metaType m
          case Map.lookup (arity, typ) varTypes of
            Just m' -> do
              sol' <- solution m'
              case sol' of
                Right _ -> return $ Map.insert (arity, typ) m varTypes
                Left l'
                  | l < l' -> do
                    solveVar m m'
                    return varTypes
                  | otherwise -> do
                    solveVar m' m
                    return varTypes
            Nothing -> return $ Map.insert (arity, typ) m varTypes
    go varTypes _ = return varTypes
    solveVar m m' = do
      (vs, _) <- instantiatedMetaType m'
      solve m'
        $ assertClosed
        $ lams (varTelescope vs)
        $ abstract (teleAbstraction vs)
        $ Meta m
        $ (\v -> (varData v, pure v)) <$> vs
    assertClosed :: Functor f => f FreeV -> f Void
    assertClosed = fmap $ error "mergeConstraintVars assertClosed"

whnf :: AbstractM -> Infer AbstractM
whnf = Normalise.whnf' Normalise.WhnfArgs
  { Normalise.expandTypeReps = False
  , Normalise.handleMetaVar = elabMetaVar
  }

whnfExpandingTypeReps :: AbstractM -> Infer AbstractM
whnfExpandingTypeReps = Normalise.whnf' Normalise.WhnfArgs
  { Normalise.expandTypeReps = True
  , Normalise.handleMetaVar = elabMetaVar
  }

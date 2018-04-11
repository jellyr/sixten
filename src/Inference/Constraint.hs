{-# LANGUAGE FlexibleContexts, OverloadedStrings, ViewPatterns #-}
module Inference.Constraint where

import Control.Monad.Except
import Control.Monad.State
import Data.Bifunctor
import Data.Foldable
import qualified Data.HashMap.Lazy as HashMap
import Data.HashMap.Lazy(HashMap)
import Data.HashSet(HashSet)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import qualified Builtin.Names as Builtin
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

isConstraintVar :: FreeV -> Bool
isConstraintVar v = case varData v of
  Constraint -> True
  Implicit -> False
  Explicit -> False

elabUnsolvedConstraint
  :: (AbstractM -> Infer AbstractM)
  -> AbstractM
  -> Infer (Maybe AbstractM)
elabUnsolvedConstraint mkConstraint typ = case typ of
  (appsView -> (Global className, _)) -> do
    -- Replace existentials in typ with universals
    (uniType, uniVarMap) <- universalise typ
    -- Try subsumption on all instances of the class until a match is found
    globalClassInstances <- liftVIX $ gets $ HashMap.lookupDefault mempty className . vixClassInstances
    locals <- localVars
    let candidates = [(Global g, bimap absurd absurd t) | (g, t) <- globalClassInstances]
          -- TODO universalise types
          <> [(pure v, varType v) | v <- toList locals, isConstraintVar v]
    matchingInstances <- withVars (HashMap.keys uniVarMap) $ forM candidates $ \(inst, instType) -> tryMaybe $ do
      f <- subtype instType uniType
      f inst
    case catMaybes matchingInstances of
      [] -> do
        logVerbose 25 "No matching instance"
        return Nothing
      matchingInstance:_ -> do
        -- Elaborate any constraints introduced by the matching instance
        elabInstance <- elabExpr mkConstraint matchingInstance
        -- Replace the universals from before with the original existentials
        result <- deuniversalise uniVarMap elabInstance
        logMeta 25 "Matching instance" result
        logMeta 25 "Matching instance typ" typ
        return $ Just result
  _ -> throwLocated "Malformed constraint" -- TODO error message

-- | Replace meta variables in typ with free variables and return the mapping
-- from the new variables to the old meta variables.
universalise :: AbstractM -> Infer (AbstractM, HashMap FreeV MetaVar)
universalise typ = undefined -- TODO
  -- second snd <$> runStateT (bindMeta go typ) mempty
  -- where
  --   go v es = do
  --     (ltr, rtl) <- get
  --     case HashMap.lookup v ltr of
  --       Nothing -> do
  --         v' <- freeVar (metaHint v) (metaType v)
  --         put (HashMap.insert v v' ltr, HashMap.insert v' v rtl)
  --         return $ pure v'
  --       Just v' -> return $ pure v'

deuniversalise :: HashMap FreeV MetaVar -> AbstractM -> Infer AbstractM
deuniversalise rtl = bindMeta go
  where
    go v = undefined -- TODO -- return $ pure $ fromMaybe v $ HashMap.lookup v rtl

elabVar
  :: (AbstractM -> Infer AbstractM)
  -> MetaVar
  -> Infer AbstractM
elabVar mkConstraint meta = do
  undefined -- TODO
  -- sol <- solution meta
  -- case (sol, metaPlicitness meta) of
  --   (Left _, Constraint) -> do
  --     mresult <- elabUnsolvedConstraint mkConstraint $ undefined $ metaType meta -- TODO
  --     case mresult of
  --       Nothing -> mkConstraint $ undefined $ metaType meta -- TODO
  --       Just result -> do
  --         solve ref $ _ result
  --         return result
  --   (Left _, Implicit) -> return $ pure var
  --   (Left _, Explicit) -> return $ pure var
  --   (Right expr, _) -> elabExpr mkConstraint expr

elabExpr
  :: (AbstractM -> Infer AbstractM)
  -> AbstractM
  -> Infer AbstractM
elabExpr mkConstraint expr = do
  undefined -- TODO
  -- logMeta 40 "elabExpr expr" expr
  -- result <- indentLog $ case expr of
  --   Builtin.UnsolvedConstraint typ -> do
  --     mresult <- elabUnsolvedConstraint mkConstraint typ
  --     case mresult of
  --       Nothing -> mkConstraint typ
  --       Just result -> return result
  --   Var v -> elabVar mkConstraint v
  --   Global g -> return $ Global g
  --   Con c -> return $ Con c
  --   Lit l -> return $ Lit l
  --   Pi h p t s -> absCase Pi h p t s
  --   Lam h p t s -> absCase Lam h p t s
  --   App e1 p e2 -> App <$> go e1 <*> pure p <*> go e2
  --   Let ds scope -> elabLet mkConstraint ds scope
  --   Case e brs t -> Case <$> go e <*> elabBranches mkConstraint brs <*> go t
  --   ExternCode ext t -> ExternCode <$> mapM go ext <*> go t
  -- logMeta 40 "elabExpr result" result
  -- return result
  -- where
  --   go = elabExpr mkConstraint
  --   absCase c h p t s = do
  --     t' <- go t
  --     v <- freeVar h t'
  --     let e = instantiate1 (pure v) s
  --     e' <- enterLevel $ withVar v $ go e
  --     let s' = abstract1 v e'
  --     return $ c h p t' s'

elabLet
  :: (AbstractM -> Infer AbstractM)
  -> LetRec (Expr MetaVar) FreeV
  -> Scope LetVar (Expr MetaVar) FreeV
  -> Infer AbstractM
elabLet mkConstraint ds scope = do
  undefined -- TODO
  -- vs <- forMLet ds $ \h _ t -> do
  --   t' <- elabExpr mkConstraint t
  --   forall h Explicit t'
  -- let abstr = letAbstraction vs
  -- ds' <- iforMLet ds $ \i h s _ -> do
  --   let e = instantiateLet pure vs s
  --   e' <- withVars vs $ elabExpr mkConstraint e
  --   s' <- abstractM abstr e'
  --   return $ LetBinding h s' $ metaType $ vs Vector.! i
  -- let expr = instantiateLet pure vs scope
  -- expr' <- withVars vs $ elabExpr mkConstraint expr
  -- scope' <- abstractM abstr expr'
  -- return $ Let (LetRec ds') scope'

elabBranches
  :: (AbstractM -> Infer AbstractM)
  -> Branches Plicitness (Expr MetaVar) FreeV
  -> Infer (Branches Plicitness (Expr MetaVar) FreeV)
elabBranches mkConstraint (ConBranches cbrs) = do
  undefined -- TODO
  -- cbrs' <- forM cbrs $ \(ConBranch qc tele brScope) -> do
  --   vs <- forTeleWithPrefixM tele $ \h p s vs -> do
  --     let t = instantiateTele pure vs s
  --     t' <- withVars vs $ elabExpr mkConstraint t -- TODO: This is a bit inefficient
  --     forall h p t'
  --   let brExpr = instantiateTele pure vs brScope
  --   brExpr' <- withVars vs $ elabExpr mkConstraint brExpr
  --   let abstr = teleAbstraction vs
  --   tele' <- Telescope
  --     <$> mapM (\v -> TeleArg (metaHint v) (metaData v) <$> abstractM abstr (metaType v)) vs
  --   brScope' <- abstractM abstr brExpr'
  --   return $ ConBranch qc tele' brScope'
  -- return $ ConBranches cbrs'
-- elabBranches mkConstraint (LitBranches lbrs def) = LitBranches
  -- <$> mapM (\(LitBranch l br) -> LitBranch l <$> elabExpr mkConstraint br) lbrs
  -- <*> elabExpr mkConstraint def

elabDef
  :: Definition (Expr MetaVar) FreeV
  -> AbstractM
  -> Infer (Definition (Expr MetaVar) FreeV)
elabDef (Definition i a e) _
  = Definition i a <$> elabExpr mkConstraintVar e
elabDef (DataDefinition (DataDef constrs) rep) typ = do
  typ' <- zonk typ
  let params = telescope typ'
  vs <- forTeleWithPrefixM params $ \h p s vs -> do
    let t = instantiateTele pure vs s
    freeVar h p t

  let abstr = teleAbstraction vs
  constrs' <- withVars vs $ forM constrs $ \constr -> forM constr $ \s -> do
    let e = instantiateTele pure vs s
    e' <- elabExpr mkConstraintVar e
    return $ abstract abstr e'

  rep' <- elabExpr mkConstraintVar rep
  return $ DataDefinition (DataDef constrs') rep'

elabRecursiveDefs
  :: Vector (FreeV, Definition (Expr MetaVar) FreeV, AbstractM)
  -> Infer (Vector (FreeV, Definition (Expr MetaVar) FreeV, AbstractM))
elabRecursiveDefs defs
  = enterLevel
  $ forM defs $ \(v, def, typ) -> do
    typ' <- elabExpr mkConstraintVar typ
    def' <- elabDef def typ'
    return (v, def', typ')

mkConstraintVar :: AbstractM -> Infer AbstractM
mkConstraintVar = exists mempty Constraint

mergeConstraintVars
  :: HashSet MetaVar
  -> Infer ()
mergeConstraintVars = undefined
  -- void . foldlM go mempty
  -- where
  --   go varTypes m@MetaVar { metaPlicitness = Constraint } = do
  --     sol <- solution m
  --     case sol of
  --       Right _ -> return varTypes
  --       Left l -> do
  --         typ <- zonk $ metaType m
  --         case Map.lookup typ varTypes of
  --           Just m' -> do
  --             sol' <- solution r'
  --             case sol' of
  --               Right _ -> return $ Map.insert typ v varTypes
  --               Left l'
  --                 | l < l' -> do
  --                   solve r' $ pure v
  --                   return $ Map.insert typ v varTypes
  --                 | otherwise -> do
  --                   solve r $ pure v'
  --                   return $ Map.insert typ v' varTypes
  --           _ -> return $ Map.insert typ v varTypes

  --   go varTypes _ = return varTypes

whnf :: AbstractM -> Infer AbstractM
whnf = Normalise.whnf' Normalise.WhnfArgs
  { Normalise.expandTypeReps = False
  , Normalise.handleUnsolvedConstraint
    = elabUnsolvedConstraint
    $ return . Builtin.UnsolvedConstraint
  }

whnfExpandingTypeReps :: AbstractM -> Infer AbstractM
whnfExpandingTypeReps = Normalise.whnf' Normalise.WhnfArgs
  { Normalise.expandTypeReps = True
  , Normalise.handleUnsolvedConstraint
    = elabUnsolvedConstraint
    $ return . Builtin.UnsolvedConstraint
  }

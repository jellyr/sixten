{-# LANGUAGE RecursiveDo #-}
module Inference.TypeCheck.Expr where

import Control.Monad.Except
import Control.Monad.ST
import Data.HashSet(HashSet)
import Data.Monoid
import Data.STRef
import qualified Data.Vector as Vector

import Analysis.Simplify
import qualified Builtin.Names as Builtin
import Inference.Constraint
import Inference.Constructor
import Inference.Match as Match
import Inference.MetaVar as MetaVar
import Inference.Monad
import Inference.Subtype
import Inference.TypeCheck.Definition
import Inference.TypeCheck.Pattern
import Inference.TypeOf
import Inference.Unify
import MonadContext
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete.Scoped as Concrete
import TypedFreeVar
import Util
import VIX

data Expected typ
  = Infer (STRef RealWorld typ) InstUntil
  | Check typ

-- | instExpected t2 t1 = e => e : t1 -> t2
instExpected :: Expected Rhotype -> Polytype -> Infer (AbstractM -> Infer AbstractM)
instExpected (Infer r instUntil) t = do
  (t', f) <- instantiateForalls t instUntil
  liftST $ writeSTRef r t'
  return f
instExpected (Check t2) t1 = subtype t1 t2

--------------------------------------------------------------------------------
-- Polytypes
checkPoly :: ConcreteM -> Polytype -> Infer AbstractM
checkPoly expr typ = do
  logPretty 20 "checkPoly expr" $ pretty <$> expr
  logMeta 20 "checkPoly type" typ
  res <- indentLog $ checkPoly' expr typ
  logMeta 20 "checkPoly res expr" res
  return res

checkPoly' :: ConcreteM -> Polytype -> Infer AbstractM
checkPoly' (Concrete.SourceLoc loc e) polyType
  = located loc $ checkPoly' e polyType
checkPoly' expr@(Concrete.Lam Implicit _ _) polyType
  = checkRho expr polyType
checkPoly' expr polyType
  = skolemise polyType (instUntilExpr expr) $ \rhoType f -> do
    e <- checkRho expr rhoType
    f e

instantiateForalls
  :: Polytype
  -> InstUntil
  -> Infer (Rhotype, AbstractM -> Infer AbstractM)
instantiateForalls typ instUntil = do
  typ' <- whnf typ
  instantiateForalls' typ' instUntil

instantiateForalls'
  :: Polytype
  -> InstUntil
  -> Infer (Rhotype, AbstractM -> Infer AbstractM)
instantiateForalls' (Abstract.Pi h p t s) instUntil
  | shouldInst p instUntil = do
    v <- existsVar h p t
    let typ = Util.instantiate1 v s
    (result, f) <- instantiateForalls typ instUntil
    return (result, \x -> f $ betaApp x p v)
instantiateForalls' typ _ = return (typ, pure)

--------------------------------------------------------------------------------
-- Rhotypes
checkRho :: ConcreteM -> Rhotype -> Infer AbstractM
checkRho expr typ = do
  logPretty 20 "checkRho expr" $ pretty <$> expr
  logMeta 20 "checkRho type" typ
  res <- indentLog $ checkRho' expr typ
  logMeta 20 "checkRho res expr" res
  return res

checkRho' :: ConcreteM -> Rhotype -> Infer AbstractM
checkRho' expr ty = tcRho expr (Check ty) (Just ty)

inferRho :: ConcreteM -> InstUntil -> Maybe Rhotype -> Infer (AbstractM, Rhotype)
inferRho expr instUntil expectedAppResult = do
  logPretty 20 "inferRho" $ pretty <$> expr
  (resExpr, resType) <- indentLog $ inferRho' expr instUntil expectedAppResult
  logMeta 20 "inferRho res expr" resExpr
  logMeta 20 "inferRho res typ" resType
  return (resExpr, resType)

inferRho' :: ConcreteM -> InstUntil -> Maybe Rhotype -> Infer (AbstractM, Rhotype)
inferRho' expr instUntil expectedAppResult = do
  ref <- liftST $ newSTRef $ error "inferRho: empty result"
  expr' <- tcRho expr (Infer ref instUntil) expectedAppResult
  typ <- liftST $ readSTRef ref
  return (expr', typ)

tcRho :: ConcreteM -> Expected Rhotype -> Maybe Rhotype -> Infer AbstractM
tcRho expr expected expectedAppResult = case expr of
  Concrete.Var v -> do
    f <- instExpected expected $ varType v
    f $ Abstract.Var v
  Concrete.Global g -> do
    (_, typ) <- definition g
    f <- instExpected expected typ
    f $ Abstract.Global g
  Concrete.Lit l -> do
    f <- instExpected expected $ typeOfLiteral l
    f $ Abstract.Lit l
  Concrete.Con cons -> do
    qc <- resolveConstr cons expectedAppResult
    typ <- qconstructor qc
    f <- instExpected expected typ
    f $ Abstract.Con qc
  Concrete.Pi p pat bodyScope -> do
    (pat', _, vs, patType) <- inferPat p pat mempty
    withVars vs $ do
      let body = instantiatePattern pure vs bodyScope
          h = Concrete.patternHint pat
      body' <- enterLevel $ checkPoly body Builtin.Type
      f <- instExpected expected Builtin.Type
      x <- freeVar h p patType
      body'' <- withVar x $ matchSingle (pure x) pat' body' Builtin.Type
      f $ Abstract.Pi h p patType $ abstract1 x body''
  Concrete.Lam p pat bodyScope -> do
    let h = Concrete.patternHint pat
    case expected of
      Infer {} -> do
        (pat', _, vs, argType) <- inferPat p pat mempty
        withVars vs $ do
          let body = instantiatePattern pure vs bodyScope
          (body', bodyType) <- enterLevel $ inferRho body (InstUntil Explicit) Nothing
          argVar <- freeVar h p argType
          body'' <- withVar argVar $ matchSingle (pure argVar) pat' body' bodyType
          let bodyScope' = abstract1 argVar body''
              bodyTypeScope = abstract1 argVar bodyType
          f <- instExpected expected $ Abstract.Pi h p argType bodyTypeScope
          f $ Abstract.Lam h p argType bodyScope'
      Check expectedType -> do
        (typeh, argType, bodyTypeScope, fResult) <- funSubtype expectedType p
        let h' = h <> typeh
        (pat', patExpr, vs) <- checkPat p pat mempty argType
        withVars vs $ do
          let body = instantiatePattern pure vs bodyScope
              bodyType = Util.instantiate1 patExpr bodyTypeScope
          body' <- enterLevel $ checkPoly body bodyType
          argVar <- freeVar h' p argType
          body'' <- withVar argVar $ matchSingle (pure argVar) pat' body' bodyType
          fResult $ Abstract.Lam h' p argType $ abstract1 argVar body''
  Concrete.App fun p arg -> do
    (fun', funType) <- inferRho fun (InstUntil p) expectedAppResult
    (argType, resTypeScope, f1) <- subtypeFun funType p
    case unusedScope resTypeScope of
      Nothing -> do
        arg' <- checkPoly arg argType
        let resType = Util.instantiate1 arg' resTypeScope
        f2 <- instExpected expected resType
        fun'' <- f1 fun'
        f2 $ Abstract.App fun'' p arg'
      Just resType -> do
        f2 <- instExpected expected resType
        arg' <- checkPoly arg argType
        fun'' <- f1 fun'
        f2 $ Abstract.App fun'' p arg'
  Concrete.Let ds scope -> enterLevel $ do
    let names = (\(_, n, _, _) -> n) <$> ds
    evars <- forM names $ \name -> do
      typ <- existsType name
      freeVar name Explicit typ
    let instantiatedDs
          = (\(loc, _, def, mtyp) ->
              ( loc
              , Concrete.TopLevelPatDefinition $ Concrete.instantiateLetClause pure evars <$> def
              , instantiateLet pure evars <$> mtyp
              )) <$> ds
    ds' <- checkRecursiveDefs False (Vector.zip evars instantiatedDs)
    let evars' = (\(v, _, _) -> v) <$> ds'
        eabstr = letAbstraction evars'
    let ds'' = LetRec
          $ flip fmap ds'
          $ \(v, Definition _ _ e, t) -> LetBinding (varHint v) (abstract eabstr e) t
    mdo
      -- let inst = instantiateLet pure vars
      vars <- iforMLet ds'' $ \i h s t -> do
        let (_, Definition a _ _, _) = ds' Vector.! i
        case a of
          Abstract -> freeVar h Explicit t
          Concrete -> freeVar h Explicit t
            -- Meta.let_ h Explicit (inst s) t -- TODO
      let abstr = letAbstraction vars
      body <- withVars vars $ tcRho (instantiateLet pure vars scope) expected expectedAppResult
      return $ Abstract.Let ds'' $ abstract abstr body
  Concrete.Case e brs -> tcBranches e brs expected expectedAppResult
  Concrete.ExternCode c -> do
    c' <- mapM (\e -> fst <$> inferRho e (InstUntil Explicit) Nothing) c
    returnType <- existsType mempty
    f <- instExpected expected returnType
    f $ Abstract.ExternCode c' returnType
  Concrete.Wildcard -> do
    t <- existsType mempty
    f <- instExpected expected t
    x <- existsVar mempty Explicit t
    f x
  Concrete.SourceLoc loc e -> located loc $ tcRho e expected expectedAppResult

tcBranches
  :: ConcreteM
  -> [(Concrete.Pat (HashSet QConstr) (PatternScope Concrete.Expr FreeV) (), PatternScope Concrete.Expr FreeV)]
  -> Expected Rhotype
  -> Maybe Rhotype
  -> Infer AbstractM
tcBranches expr pbrs expected expectedAppResult = do
  (expr', exprType) <- inferRho expr (InstUntil Explicit) Nothing

  inferredPats <- forM pbrs $ \(pat, brScope) -> do
    (pat', _, vs) <- checkPat Explicit (void pat) mempty exprType
    let br = instantiatePattern pure vs brScope
    return (pat', br)

  (inferredBranches, resType) <- case expected of
    Check resType -> do
      brs <- forM inferredPats $ \(pat, br) -> do
        br' <- checkRho br resType
        return (pat, br')
      return (brs, resType)
    Infer _ instUntil -> do
      resType <- existsType mempty
      brs <- forM inferredPats $ \(pat, br) -> do
        (br', brType) <- inferRho br instUntil expectedAppResult
        unify mempty brType resType
        return (pat, br')
      return (brs, resType)

  f <- instExpected expected resType

  matched <- matchCase expr' inferredBranches resType
  f matched

{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Inference.TypeCheck.Definition where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable as Foldable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.Monoid
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import {-# SOURCE #-} Inference.TypeCheck.Expr
import Analysis.Simplify
import qualified Builtin.Names as Builtin
import Inference.Constraint
import Inference.Cycle
import Inference.MetaVar
import Inference.MetaVar.Zonk
import Inference.Monad
import Inference.TypeCheck.Clause
import Inference.TypeCheck.Data
import Inference.Unify
import MonadContext
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete.Scoped as Concrete
import TypedFreeVar
import Util
import qualified Util.MultiHashMap as MultiHashMap
import Util.TopoSort
import VIX

checkDefType
  :: Concrete.PatDefinition (Concrete.Clause Void Concrete.Expr FreeV)
  -> AbstractM
  -> Infer (Definition (Abstract.Expr MetaVar) FreeV, AbstractM)
checkDefType (Concrete.PatDefinition a i clauses) typ = do
  e' <- checkClauses clauses typ
  return (Definition a i e', typ)

checkTopLevelDefType
  :: FreeV
  -> Concrete.TopLevelPatDefinition Concrete.Expr FreeV
  -> SourceLoc
  -> AbstractM
  -> Infer (Definition (Abstract.Expr MetaVar) FreeV, AbstractM)
checkTopLevelDefType v def loc typ = located loc $ case def of
  Concrete.TopLevelPatDefinition def' -> checkDefType def' typ
  Concrete.TopLevelPatDataDefinition d -> checkDataType v d typ
  -- Should be removed by Declassify:
  Concrete.TopLevelPatClassDefinition _ -> error "checkTopLevelDefType class"
  Concrete.TopLevelPatInstanceDefinition _ -> error "checkTopLevelDefType instance"

abstractDef
  :: Foldable t
  => t FreeV
  -> Definition (Abstract.Expr MetaVar) FreeV
  -> AbstractM
  -> (Definition (Abstract.Expr MetaVar) FreeV, AbstractM)
abstractDef vs (Definition a i e) t = do
  let ge = abstract1s vs Abstract.Lam e
      gt = abstract1s vs Abstract.Pi t
  (Definition a i ge, gt)
abstractDef vs (DataDefinition (DataDef cs) rep) typ = do
  let cs' = map (fmap $ toScope . splat f g) cs
  -- Abstract vs on top of typ
  let grep = abstract1s vs Abstract.Lam rep
      gtyp = abstract1s vs Abstract.Pi typ
  (DataDefinition (DataDef cs') grep, gtyp)
  where
    varIndex = hashedElemIndex $ toVector vs
    f v = pure $ maybe (F v) (B . TeleVar) (varIndex v)
    g = pure . B . (+ TeleVar (length vs))

abstract1s
  :: Foldable t
  => t FreeV
  -> (NameHint -> Plicitness -> AbstractM -> Scope () (Abstract.Expr MetaVar) FreeV -> AbstractM)
  -> AbstractM
  -> AbstractM
abstract1s vs c b = foldr
  (\v s -> c (varHint v) (varData v) (varType v) $ abstract1 v s)
  b
  vs

data GeneraliseDefsMode
  = GeneraliseType
  | GeneraliseAll
  deriving (Eq, Show)

generaliseMetas
  :: HashSet MetaVar
  -> Infer (HashMap MetaVar FreeV)
generaliseMetas metas = do
  instMetas <- forM (toList metas) $ \m -> do
    (instVs, instTyp) <- instantiatedMetaType m
    deps <- metaVars instTyp
    return (m, (instVs, instTyp, deps))

  let sortedMetas = acyclic <$> topoSortWith fst (thd3 . snd) instMetas

  flip execStateT mempty $ forM_ sortedMetas $ \(m, (instVs, instTyp, _deps)) -> do
    sub <- get
    instTyp' <- bindMetas (\m es -> return $ case HashMap.lookup m sub of
      Nothing -> Abstract.Meta m es
      Just v -> pure v
      ) instTyp
    let localDeps = toHashSet instTyp' `HashSet.intersection` instVs
    unless (HashSet.null localDeps) $ error "generaliseMetas local deps" -- TODO error message
    v <- freeVar (metaHint m) (metaPlicitness m) instTyp'
    modify $ HashMap.insert m v
    return ()
  where
    acyclic (AcyclicSCC a) = a
    acyclic (CyclicSCC _) = error "generaliseMetas"

    instantiatedMetaType
      :: MetaVar
      -> Infer (HashSet FreeV, AbstractM)
    instantiatedMetaType m = go mempty (metaArity m) (vacuous $ metaType m)
      where
        go vs 0 t = return (vs, t)
        go vs n (Abstract.Pi h a t s) = do
          v <- freeVar h a t
          go (HashSet.insert v vs) (n - 1) (instantiate1 (pure v) s)

generaliseDefs
  :: GeneraliseDefsMode
  -> Vector
    ( FreeV
    , Definition (Abstract.Expr MetaVar) FreeV
    , AbstractM
    )
  -> Infer
    ( Vector
      ( FreeV
      , Definition (Abstract.Expr MetaVar) FreeV
      , AbstractM
      )
    , FreeV -> FreeV
    )
generaliseDefs mode defs = indentLog $ do
  -- After type-checking we may actually be in a situation where a dependency
  -- we thought existed doesn't actually exist because of class instances being
  -- resolved (unresolved class instances are assumed to depend on all
  -- instances), so we can't be sure that we have a single cycle. Therefore we
  -- separately compute dependencies for each definition.
  let vars = (\(v, _, _) -> v) <$> defs

      defFreeVars = case mode of
        GeneraliseType -> mempty
        GeneraliseAll -> MultiHashMap.fromMultiList [(v, toHashSet def) | (v, def, _) <- Vector.toList defs]

      typeFreeVars = MultiHashMap.fromMultiList [(v, toHashSet t) | (v, _, t) <- Vector.toList defs]

  outerLocals <- toHashSet <$> localVars

  outerLevel <- level

  let isLocalConstraint m@MetaVar { metaPlicitness = Constraint } = isLocalMeta m
      isLocalConstraint _ = return False

      isLocalMeta m = either (>= outerLevel) (const False) <$> solution m

  defVars <- case mode of
    GeneraliseType -> return mempty
    GeneraliseAll -> forM defs $ \(v, def, _) -> do
      let fvs = toHashSet def
      metas <- filterMSet isLocalConstraint =<< definitionMetaVars def
      return (v, (fvs, metas))

  typeVars <- forM defs $ \(v, _, typ) -> do
    let fvs = toHashSet typ
    metas <- filterMSet isLocalMeta =<< metaVars typ
    return (v, (fvs, metas))

  let satDefVars = saturateMap fst $ toHashMap defVars
      satTypeVars = saturateMap fst $ toHashMap typeVars

  let defAndTypeVars = Vector.zipWith (<>) defVars typeVars
      metas = fold $ snd . snd <$> defAndTypeVars

  mergeConstraintVars metas
  -- forM_ allMetas generalise
    -- TODO: check that fvs of metaGeneraliser is a subset of the free vars in context

  metaSub <- generaliseMetas metas

  sortedMetas <- forM defAndTypeVars $ \ms -> do

    deps <- forM (toList ms) $ \m -> do
      t' <- zonk $ metaType m
      ds <- metaVars t'
      return (m, ds)

    let sortedMs = acyclic <$> topoSort deps

    return [(implicitise $ metaPlicitness m, v) | m <- sortedMs]

  let lookupMetas = hashedLookup $ Vector.zip vars sortedMetas
      sub v = maybe (pure v) (Abstract.apps (pure v) . fmap (second pure)) $ lookupMetas v

  instDefs <- forM defs $ \(v, d, t) -> do
    let d' = d >>>= sub
        t' = t >>= sub
    return (v, d', t')

  genDefs <- forM (Vector.zip sortedMetas instDefs) $ \(fvs, (v, d, t)) -> do
    let (d', t') = abstractDef (snd <$> fvs) d t
    return (v, d', t')

  newVars <- forM genDefs $ \(v, _, t) ->
    freeVar (varHint v) (varData v) t

  let lookupNewVar = hashedLookup $ Vector.zip vars newVars
      newVarSub v = fromMaybe v $ lookupNewVar v

  let newVarDefs = flip fmap (Vector.zip newVars genDefs) $ \(v, (_, d, t)) ->
        (v, newVarSub <$> d, newVarSub <$> t)

  return (newVarDefs, newVarSub)
  where
    acyclic (AcyclicSCC a) = a
    acyclic (CyclicSCC _) = error "generaliseDefs"

checkRecursiveDefs
  :: Bool
  -> Vector
    ( FreeV
    , ( SourceLoc
      , Concrete.TopLevelPatDefinition Concrete.Expr FreeV
      , Maybe ConcreteM
      )
    )
  -> Infer
    (Vector
      ( FreeV
      , Definition (Abstract.Expr MetaVar) FreeV
      , AbstractM
      )
    )
checkRecursiveDefs forceGeneralisation defs = do
  -- Divide the definitions into ones with and without type signature.
  let (noSigDefs, sigDefs) = divide defs

  -- Assume that the specified type signatures are correct.
  sigDefs' <- forM sigDefs $ \(evar, (loc, def, typ)) -> do
    typ' <- checkPoly typ Builtin.Type
    unify [] (varType evar) typ'
    return (evar, (loc, def))

  -- withVars (fst <$> defs) $ do
  do

    -- The definitions without type signature are checked and generalised,
    -- assuming the type signatures of the others.
    noSigResult <- checkAndElabDefs noSigDefs

    result <- if forceGeneralisation || shouldGeneralise defs then do

      -- Generalise the definitions without signature
      (genNoSigResult, noSigSub) <- generaliseDefs GeneraliseAll noSigResult

      subbedSigDefs <- forM sigDefs' $ \(v, (loc, def)) -> do
        let def' = def >>>= pure . noSigSub
        return (v, (loc, def'))

      sigResult <- checkAndElabDefs subbedSigDefs

      -- Generalise the definitions with signature
      if Vector.null sigResult then
          -- No need to generalise again if there are actually no definitions
          -- with signatures
          return genNoSigResult
        else do
          (genResult, _) <- generaliseDefs GeneraliseType $ genNoSigResult <> sigResult
          return genResult
    else do
      sigResult <- checkAndElabDefs sigDefs'
      return $ noSigResult <> sigResult

    let locs = (\(_, (loc, _)) -> loc) <$> noSigDefs
          <|> (\(_, (loc, _)) -> loc) <$> sigDefs'

    unless (Vector.length locs == Vector.length result) $
      internalError $ "checkRecursiveDefs unmatched length" PP.<+> shower (Vector.length locs) PP.<+> shower (Vector.length result)

    let locResult = Vector.zip locs result

    detectTypeRepCycles locResult
    detectDefCycles locResult

    let permutation = Vector.zip (fst <$> defs) (fst <$> noSigDefs <|> fst <$> sigDefs)
    return $ unpermute permutation result
  where
    divide = bimap Vector.fromList Vector.fromList . foldMap go
      where
        go (v, (loc, def, Nothing)) = ([(v, (loc, def))], [])
        go (v, (loc, def, Just t)) = ([], [(v, (loc, def, t))])

checkAndElabDefs
  :: Vector
    ( FreeV
    , ( SourceLoc
      , Concrete.TopLevelPatDefinition Concrete.Expr FreeV
      )
    )
  -> Infer
    (Vector
      ( FreeV
      , Definition (Abstract.Expr MetaVar) FreeV
      , AbstractM
      )
    )
checkAndElabDefs defs = indentLog $ do
  -- forM_ defs $ \(var, (_, def)) ->
  --   logMeta 20 ("checkAndElabDefs " ++ show (pretty $ fromNameHint "" id $ varHint var)) def

  checkedDefs <- forM defs $ \(var, (loc, def)) -> do
    (def', typ'') <- checkTopLevelDefType var def loc $ varType var
    return (loc, (var, def', typ''))

  elabDefs <- elabRecursiveDefs $ snd <$> checkedDefs

--   forM_ elabDefs $ \(var, def, typ) -> do
--     logMeta 20 ("checkAndElabDefs res " ++ show (pretty $ fromNameHint "" id $ metaHint var)) def
--     logMeta 20 ("checkAndElabDefs res t " ++ show (pretty $ fromNameHint "" id $ metaHint var)) typ

  return elabDefs

shouldGeneralise
  :: Vector
    ( FreeV
    , ( SourceLoc
      , Concrete.TopLevelPatDefinition Concrete.Expr FreeV
      , Maybe ConcreteM
      )
    )
  -> Bool
shouldGeneralise = all (\(_, (_, def, _)) -> shouldGeneraliseDef def)
  where
    shouldGeneraliseDef (Concrete.TopLevelPatDefinition (Concrete.PatDefinition _ _ (Concrete.Clause ps _ NonEmpty.:| _))) = Vector.length ps > 0
    shouldGeneraliseDef Concrete.TopLevelPatDataDefinition {} = True
    shouldGeneraliseDef Concrete.TopLevelPatClassDefinition {} = True
    shouldGeneraliseDef Concrete.TopLevelPatInstanceDefinition {} = True

checkTopLevelRecursiveDefs
  :: Vector
    ( QName
    , SourceLoc
    , Concrete.TopLevelPatDefinition Concrete.Expr Void
    , Maybe (Concrete.Type Void)
    )
  -> Infer
    (Vector
      ( QName
      , Definition (Abstract.Expr Void) Void
      , Abstract.Type Void Void
      )
    )
checkTopLevelRecursiveDefs defs = do
  let names = (\(v, _, _, _) -> v) <$> defs

  checkedDefs <- enterLevel $ do
    vars <- forM names $ \name -> do
      let hint = fromQName name
      typ <- existsType hint
      freeVar hint Explicit typ

    let nameIndex = hashedElemIndex names
        expose name = case nameIndex name of
          Nothing -> global name
          Just index -> pure
            $ fromMaybe (error "checkTopLevelRecursiveDefs 1")
            $ vars Vector.!? index

    let exposedDefs = flip fmap defs $ \(_, loc, def, mtyp) ->
          (loc, gbound expose $ vacuous def, gbind expose . vacuous <$> mtyp)

    checkRecursiveDefs True (Vector.zip vars exposedDefs)

  let vars' = (\(v, _, _) -> v) <$> checkedDefs

  l <- level
  let varIndex = hashedElemIndex vars'
      unexpose v = fromMaybe (pure v) $ (fmap global . (names Vector.!?)) =<< varIndex v
      vf :: FreeV -> Infer b
      vf v = internalError $ "checkTopLevelRecursiveDefs" PP.<+> shower v PP.<+> shower l
      mf :: MetaVar -> Infer b
      mf v = internalError $ "checkTopLevelRecursiveDefs" PP.<+> shower v PP.<+> shower l

  forM (Vector.zip names checkedDefs) $ \(name, (_, def, typ)) -> do
    let unexposedDef = def >>>= unexpose
        unexposedTyp = typ >>= unexpose
    -- logMeta 20 ("checkTopLevelRecursiveDefs unexposedDef " ++ show (pretty name)) unexposedDef
    logMeta 20 ("checkTopLevelRecursiveDefs unexposedTyp " ++ show (pretty name)) unexposedTyp
    unexposedDef' <- bitraverseDefinition mf vf unexposedDef
    unexposedTyp' <- bitraverse mf vf unexposedTyp
    return (name, unexposedDef', unexposedTyp')

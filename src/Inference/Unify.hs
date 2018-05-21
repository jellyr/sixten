{-# LANGUAGE FlexibleContexts, OverloadedStrings, ViewPatterns #-}
module Inference.Unify where

import Control.Monad.Except
import Data.Bifoldable
import Data.Bifunctor
import Data.Foldable
import qualified Data.HashSet as HashSet
import Data.HashSet(HashSet)
import Data.List
import Data.Monoid
import Data.STRef
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Vector as Vector
import Data.Void

import Analysis.Simplify
import Inference.MetaVar
import Inference.MetaVar.Zonk
import Inference.Monad
import Inference.Normalise
import Inference.TypeOf
import MonadContext
import Pretty
import Syntax
import Syntax.Abstract
import TypedFreeVar
import Util
import VIX

occurs
  :: [(AbstractM, AbstractM)]
  -> Level
  -> MetaVar
  -> AbstractM
  -> Infer ()
occurs cxt l mv expr = bitraverse_ go pure expr
  where
    go mv'
      | mv == mv' = do
        explanation <- forM cxt $ \(t1, t2) -> do
          t1' <- zonk t1
          t2' <- zonk t2
          actual <- prettyMeta t1'
          expect <- prettyMeta t2'
          return
            [ ""
            , bold "Inferred:" PP.<+> red actual
            , bold "Expected:" PP.<+> dullGreen expect
            ]
        printedTv <- prettyMetaVar mv'
        expr' <- zonk expr
        printedExpr <- prettyMeta expr'
        throwLocated
          $ "Cannot construct the infinite type"
          <> PP.line
          <> PP.vcat
            ([ dullBlue printedTv
            , "="
            , dullBlue printedExpr
            , ""
            , "while trying to unify"
            ] ++ intercalate ["", "while trying to unify"] explanation)
      | otherwise = do
        occurs cxt l mv $ vacuous $ metaType mv'
        sol <- solution mv
        case sol of
          Left l' -> liftST $ writeSTRef (metaRef mv') $ Left $ min l l'
          Right expr' -> traverse_ go $ vacuous expr'

prune :: HashSet FreeV -> AbstractM -> Infer AbstractM
prune allowed expr = do
  outerContext <- toHashSet <$> localVars
  let go m es = do
        sol <- solution m
        case sol of
          Right e -> bindMetas go $ betaApps (vacuous e) es
          Left l -> do
            innerContext <- toHashSet <$> localVars
            case distinctVars es of
              Nothing -> return $ Meta m es
              Just vs
                | Vector.length vs' == Vector.length vs -> return $ Meta m es
                | otherwise -> do
                  let m'Type = pis (varTelescope vs') $ abstract (teleAbstraction vs') mType
                  m'Type' <- bindMetas go m'Type
                  let typeFvs = toHashSet m'Type'
                  if HashSet.null typeFvs then do
                    m' <- existsAtLevel
                      (metaHint m)
                      (metaPlicitness m)
                      (assertClosed m'Type')
                      (Vector.length vs')
                      l
                    let e = Meta m' $ (\v -> (varData v, pure v)) <$> vs'
                    solve m $ assertClosed $ lams (varTelescope vs) $ abstract (teleAbstraction vs) e
                    return e
                  else
                    return $ Meta m es
                | otherwise -> return $ Meta m es
                where
                  assertClosed :: Functor f => f FreeV -> f Void
                  assertClosed = fmap $ error "prune assertClosed"
                  allowed' = allowed <> innerContext `HashSet.difference` outerContext
                  vs' = Vector.filter (`HashSet.member` allowed') vs
                  Just mType = typeApps (vacuous $ metaType m) es

  bindMetas go expr

unify :: [(AbstractM, AbstractM)] -> AbstractM -> AbstractM -> Infer ()
unify cxt type1 type2 = do
  logMeta 30 "unify t1" type1
  logMeta 30 "      t2" type2
  type1' <- zonk =<< whnf type1
  type2' <- zonk =<< whnf type2
  unify' ((type1', type2') : cxt) type1' type2'

unify' :: [(AbstractM, AbstractM)] -> AbstractM -> AbstractM -> Infer ()
unify' cxt type1 type2
  | type1 == type2 = return () -- TODO make specialised equality function to get rid of zonking in this and subtyping
  | otherwise = case (type1, type2) of
    -- TODO Handle same metavariable with different args
    -- See Higher-Order Dynamic Pattern Unification for Dependent Types and Records

    -- If we have 'unify (f xs) t', where 'f' is an existential, and 'xs' are
    -- distinct universally quantified variables, then 'f = \xs. t' is a most
    -- general solution (see Miller, Dale (1991) "A Logic programming...")
    (Meta m (distinctVars -> Just vs), _) -> solveVar unify m vs type2
    (_, Meta m (distinctVars -> Just vs)) -> solveVar (flip . unify) m vs type1
    (Pi h1 p1 t1 s1, Pi h2 p2 t2 s2) | p1 == p2 -> absCase (h1 <> h2) p1 t1 t2 s1 s2
    (Lam h1 p1 t1 s1, Lam h2 p2 t2 s2) | p1 == p2 -> absCase (h1 <> h2) p1 t1 t2 s1 s2
    -- Since we've already tried reducing the application, we can only hope to
    -- unify it pointwise.
    (App e1 p1 e1', App e2 p2 e2') | p1 == p2 -> do
      unify cxt e1  e2
      unify cxt e1' e2'
    _ -> do
      explanation <- forM cxt $ \(t1, t2) -> do
        t1' <- zonk t1
        t2' <- zonk t2
        actual <- prettyMeta t1'
        expect <- prettyMeta t2'
        return
          [ ""
          , bold "Inferred:" PP.<+> red actual
          , bold "Expected:" PP.<+> dullGreen expect
          ]
      throwLocated
        $ "Type mismatch" <> PP.line <>
          PP.vcat (intercalate ["", "while trying to unify"] explanation)
  where
    absCase h p t1 t2 s1 s2 = do
      unify cxt t1 t2
      v <- freeVar h p t1
      withVar v $ unify cxt (instantiate1 (pure v) s1) (instantiate1 (pure v) s2)
    solveVar recurse m vs t = do
      sol <- solution m
      case sol of
        Left l -> do
          t' <- normalise =<< prune (toHashSet vs) t
          occurs cxt l m t'
          let tele = varTelescope vs
              abstr = teleAbstraction vs
              lamt = lams tele $ abstract abstr t'
          lamtType <- typeOf lamt
          lamt' <- traverse (error "Unify TODO error message") lamt
          recurse cxt (vacuous $ metaType m) lamtType
          logMeta 30 ("solving " <> show (metaId m)) lamt
          solve m lamt'
        Right c -> recurse cxt (apps (vacuous c) $ (\v -> (varData v, pure v)) <$> vs) t

distinctVars es = case traverse isVar es of
  Just es' | distinct es' -> Just es'
  _ -> Nothing

isVar (_, Var v) = Just v
isVar _ = Nothing
distinct es = HashSet.size (toHashSet es) == length es

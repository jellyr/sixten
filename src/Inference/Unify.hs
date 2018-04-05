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

import Inference.MetaVar
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
    go mv'@(MetaVar _ typ _ r _)
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
        occurs cxt l mv $ vacuous typ
        sol <- solution mv
        case sol of
          Left l' -> liftST $ writeSTRef r $ Left $ min l l'
          Right expr' -> traverse_ go $ vacuous expr'

prune :: HashSet FreeV -> AbstractM -> Infer ()
prune allowed expr = case expr of
  Var _ -> return ()
  Meta m (distinctVars -> Just vs) -> do
    let vs' = Vector.filter (`HashSet.member` allowed) vs
    undefined
  Meta _ es -> mapM_ (prune allowed . snd) es
  Global _ -> return ()
  Con _ -> return ()
  Lit _ -> return ()
  Pi h p t s -> absCase h p t s
  Lam h p t s -> absCase h p t s
  App e1 _ e2 -> do
    prune allowed e1
    prune allowed e2
  Let _ _ -> return () -- TODO
  Case _ _ _ -> return () -- TODO
  ExternCode _ _ -> return () -- TODO
  where
    absCase h p t s = do
      prune allowed t
      v <- freeVar h p t
      prune (HashSet.insert v allowed) $ instantiate1 (pure v) s

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
    -- TODO what to do with equal metavariables with different args?
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
          prune (toHashSet vs) t
          t' <- zonk =<< normalise t
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

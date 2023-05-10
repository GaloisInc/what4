------------------------------------------------------------------------
-- |
-- Module      : What4.Expr.Fuzz
-- Description : Fuzz expressions
-- Copyright   : (c) Galois, Inc 2023
-- License     : BSD3
-- Maintainer  : Andrei Stefanescu <andrei@galois.com>
-- Stability   : provisional
--
-- Given a collection of assignments to the symbolic values appearing in
-- an expression, this module computes the ground value.
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}


module What4.Expr.Fuzz
  ( evaluateExpr
  , simplifyExpr
  , getEquivalenceClasses
  , EquivalenceClass(..)
  ) where


import           Control.Monad.IO.Class
import           Control.Monad.ST
import           Control.Monad.State
import           Data.Foldable
import           Data.Kind
import           Data.Maybe
import           Data.Set (Set)
import qualified Data.Set as Set
import           GHC.Exts (IsList)
import qualified System.Random as Random

import           Data.Parameterized
import qualified Data.Parameterized.HashTable as PH
import qualified Data.Parameterized.Map as PM
import           Data.Parameterized.Nonce

import           What4.Expr.App
import           What4.Expr.Builder
import           What4.Expr.GroundEval
import           What4.Interface
import           What4.Panic (panic)
import           What4.Protocol.SMTLib2
import           What4.SatResult
import           What4.Solver.Adapter
import qualified What4.Solver.Z3 as Z3


evaluateExpr ::
  forall t st fs tp m .
  (MonadIO m, MonadFail m) =>
  ExprBuilder t st fs ->
  Int ->
  Integer ->
  Expr t tp ->
  m (GroundValue tp, IdxCache t (TypedWrapper GroundValueWrapper))
evaluateExpr sym seed bound expr = do
  let ?bound = bound
  let ?rand_on_fail = False
  c <- newIdxCache
  let ?cache = c
  val <- evalStateT (evalGroundExprStep sym expr) (Random.mkStdGen seed)
  return (val, ?cache)

evalGroundExprStep ::
  (MonadIO m, MonadFail m, ?bound :: Integer, ?rand_on_fail :: Bool, ?cache :: IdxCache t (TypedWrapper GroundValueWrapper)) =>
  ExprBuilder t st fs ->
  Expr t tp ->
  StateT Random.StdGen m (GroundValue tp)
evalGroundExprStep sym = typedCachedEvalGroundExpr $ \e ->
  if| BoundVarExpr{} <- e ->
      randomGroundValue (exprType e)
    | Just (FnApp fn args) <- asNonceApp e -> do
      ground_args <- traverseFC (\arg -> mkGroundExpr sym (exprType arg) =<< evalGroundExprStep sym arg) args
      ground_fn_app <- liftIO $ applySymFn sym fn ground_args
      fmap (unGVW . unwrapTyped) $ idxCacheEval ?cache ground_fn_app $ fmap (TypedWrapper (exprType e) . GVW) $ do
        randomGroundValue (exprType e)
    | otherwise ->
      if ?rand_on_fail then
        randomGroundValue (exprType e)
      else
        fail $ "fuzzExpr: unexpected expression: " ++ show e


simplifyExpr ::
  (MonadIO m, MonadFail m) =>
  ExprBuilder t st fs ->
  Int ->
  Integer ->
  Int ->
  Expr t tp ->
  m (Expr t tp)
simplifyExpr sym seed bound rounds expr = do
  equiv_classes <- getEquivalenceClasses sym seed bound rounds expr
  let subst_pairs = foldMap (viewSome equivalenceClassNormalSubstitutionPairs) equiv_classes
  applySubstitutionPairs sym subst_pairs expr


newtype EquivalenceClass t tp = EquivalenceClass (Expr t tp, [Expr t tp])
  deriving (Eq, Ord, Show)

equivalenceClassNormalSubstitutionPairs :: EquivalenceClass t tp -> [Pair (Expr t) (Expr t)]
equivalenceClassNormalSubstitutionPairs (EquivalenceClass (class_expr, exprs)) = map (\e -> Pair e class_expr) exprs

getEquivalenceClasses ::
  (MonadIO m, MonadFail m) =>
  ExprBuilder t st fs ->
  Int ->
  Integer ->
  Int ->
  Expr t tp ->
  m [Some (EquivalenceClass t)]
getEquivalenceClasses sym seed bound rounds expr = do
  nonce_candidates <- getEquivalenceClassesCandidates sym seed bound rounds expr
  nonce_expr_tbl <- getNonceExprTable expr

  liftIO $ Z3.withZ3 sym "z3" defaultLogData $ \session -> do
    foldl (<>) [] <$> mapM
      (\(Some s) -> fmap Some <$> splitEquivalenceClassCandidate sym session nonce_expr_tbl s)
      nonce_candidates

getEquivalenceClassesCandidates ::
  (MonadIO m, MonadFail m) =>
  ExprBuilder t st fs ->
  Int ->
  Integer ->
  Int ->
  Expr t tp ->
  m [Some (TypedWrapper (SetF (Nonce t)))]
getEquivalenceClassesCandidates sym seed bound rounds expr = do
  eval_caches <- evalStateT (replicateM rounds $ lalala sym bound expr) (Random.mkStdGen seed)
  case eval_caches of
    head_cache : tail_caches ->
      return $ Set.toList $ Set.fromList $ PM.elems $ foldl' intersectionMultimap head_cache tail_caches
    [] -> fail $ "getEquivalenceClassesCandidates: empty eval_caches, rounds = " ++ show rounds

lalala ::
  forall t st fs tp m .
  (MonadIO m, MonadFail m) =>
  ExprBuilder t st fs ->
  Integer ->
  Expr t tp ->
  StateT Random.StdGen m (PM.MapF @BaseType (Nonce t) (TypedWrapper (SetF (Nonce t))))
lalala sym bound expr = do
  let ?bound = bound
  let ?rand_on_fail = True
  c <- newIdxCache
  let ?cache = c

  _ <- evalGroundExprStep sym expr

  keyEquivalenceClasses <$> getIdxCache ?cache

splitEquivalenceClassCandidate ::
  forall t st fs tp a m .
  (SMTLib2Tweaks a, MonadIO m) =>
  ExprBuilder t st fs ->
  Session t a ->
  PH.HashTable RealWorld (Nonce t) (Expr t) ->
  TypedWrapper (SetF (Nonce t)) tp ->
  m [EquivalenceClass t tp]
splitEquivalenceClassCandidate sym session nonce_expr_tbl (TypedWrapper _tp (SetF nonces)) = do
  let splitEquivalenceClassCandidateRec ::
        [EquivalenceClass t tp] ->
        Expr t tp ->
        m [EquivalenceClass t tp]
      splitEquivalenceClassCandidateRec classes expr = case classes of
        [] -> return [EquivalenceClass (expr, [])]
        head_class@(EquivalenceClass (class_expr, class_extra_exprs)) : tail_classes -> do
          res <- checkExprEqSat sym session class_expr expr
          if isUnsat res then
            return $ EquivalenceClass (class_expr, expr : class_extra_exprs) : tail_classes
          else do
            tail_classes' <- splitEquivalenceClassCandidateRec tail_classes expr 
            return $ head_class : tail_classes'

  exprs <- mapM
    (fmap (fromMaybe $ panic "splitEquivalenceClassesCandidates" ["nonce not found"]) .
      liftIO . stToIO . PH.lookup nonce_expr_tbl)
    (Set.toList nonces)
  foldlM splitEquivalenceClassCandidateRec [] exprs


newtype SetF (e :: k -> Type) (tp :: k) = SetF (Set (e tp))
  deriving (Eq, Ord, Show, Semigroup, Monoid, IsList)

instance (forall tp . Eq (SetF e tp)) => TypedEq (SetF e)
instance (forall tp . Ord (SetF e tp)) => TypedOrd (SetF e)
instance (forall tp . Show (SetF e tp)) => TypedShow (SetF e)
instance FoldableFC SetF where
  foldMapFC f (SetF s) = foldMap f s

unionTypedSetF ::
  Ord (e tp) =>
  TypedWrapper (SetF e) tp ->
  TypedWrapper (SetF e) tp ->
  TypedWrapper (SetF e) tp
unionTypedSetF (TypedWrapper tp (SetF s1)) (TypedWrapper _ (SetF s2)) =
  TypedWrapper tp $ SetF $ Set.union s1 s2

intersectionTypedSetF ::
  Ord (e tp) =>
  TypedWrapper (SetF e) tp ->
  TypedWrapper (SetF e) tp ->
  TypedWrapper (SetF e) tp
intersectionTypedSetF (TypedWrapper tp (SetF s1)) (TypedWrapper _ (SetF s2)) =
  TypedWrapper tp $ SetF $ Set.intersection s1 s2


reverseMap ::
  (forall tp . Ord (k tp), OrdF v, IsTyped v) =>
  PM.MapF k v ->
  PM.MapF v (TypedWrapper (SetF k))
reverseMap =
  PM.foldrWithKey'
    (\k v ->
      PM.insertWith unionTypedSetF v $ TypedWrapper (baseTypeRepr v) $ SetF $ Set.singleton k)
    PM.empty

intersectionMultimap ::
  (OrdF k, forall tp . Ord (v tp)) =>
  PM.MapF k (TypedWrapper (SetF v)) ->
  PM.MapF k (TypedWrapper (SetF v)) ->
  PM.MapF k (TypedWrapper (SetF v))
intersectionMultimap = PM.intersectWithKeyMaybe (\_ x y -> Just $ intersectionTypedSetF x y)

keyEquivalenceClasses ::
  (OrdF k, forall tp . Ord (k tp), OrdF v, IsTyped v) =>
  PM.MapF k v ->
  PM.MapF k (TypedWrapper (SetF k))
keyEquivalenceClasses m = PM.mapMaybe (\v -> PM.lookup v (reverseMap m)) m

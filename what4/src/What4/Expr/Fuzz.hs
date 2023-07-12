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

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE UndecidableInstances #-}


module What4.Expr.Fuzz
  ( evaluateExpr
  , evaluateExprWithOptions
  , simplifyExpr
  , simplifyExprWithOptions
  , getEquivalenceClasses
  , FuzzOptions(..)
  , defaultFuzzOptions
  ) where


import           Control.Monad.IO.Class
import           Control.Monad.ST
import           Control.Monad.State
import           Data.Foldable
import           Data.Foldable.Extra
import           Data.Kind
import qualified Data.List as List
import           Data.Maybe
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified System.Random as Random

import           Data.Parameterized
import qualified Data.Parameterized.HashTable as PH
import qualified Data.Parameterized.Map as PM
import           Data.Parameterized.Nonce

import           What4.Config
import           What4.Expr.App
import           What4.Expr.Builder
import           What4.Expr.GroundEval
import           What4.Interface
import           What4.Panic (panic)
import           What4.Protocol.SMTWriter
import           What4.Protocol.Online
import           What4.SatResult
import           What4.Solver.Adapter
import           What4.Solver.CVC5
import           What4.Solver.Yices
import           What4.Solver.Z3


data FuzzOptions st = FuzzOptions
  { fuzzSeed :: Int
  , fuzzBound :: Integer
  , fuzzRounds :: Int
  , fuzzAdapter :: SolverAdapter st
  , fuzzVariableAbstraction :: Bool
  , fuzzFail :: Bool
  }
  deriving (Eq, Ord, Show)

defaultFuzzOptions :: FuzzOptions st
defaultFuzzOptions = FuzzOptions
  { fuzzSeed = 0
  , fuzzBound = 1000
  , fuzzRounds = 10
  , fuzzAdapter = yicesAdapter
  , fuzzVariableAbstraction = True
  , fuzzFail = True
  }

type FuzzConstraints st =
  ( ?seed :: Int
  , ?bound :: Integer
  , ?rounds :: Int
  , ?adapter :: SolverAdapter st
  , ?variableAbstraction :: Bool
  , ?fail :: Bool
  )

withFuzzConstraints :: FuzzOptions st -> (FuzzConstraints st => a) -> a
withFuzzConstraints opts a = do
  let ?seed = fuzzSeed opts
  let ?bound = fuzzBound opts
  let ?rounds = fuzzRounds opts
  let ?adapter = fuzzAdapter opts
  let ?variableAbstraction = fuzzVariableAbstraction opts
  let ?fail = fuzzFail opts
  a


evaluateExpr ::
  (MonadIO m, MonadFail m) =>
  ExprBuilder t st fs ->
  Expr t tp ->
  m [GroundValue tp]
evaluateExpr = evaluateExprWithOptions defaultFuzzOptions

evaluateExprWithOptions ::
  (MonadIO m, MonadFail m) =>
  FuzzOptions st ->
  ExprBuilder t st fs ->
  Expr t tp ->
  m [GroundValue tp]
evaluateExprWithOptions opts sym expr = withFuzzConstraints opts $ do
  map fst <$> evaluateGroundExpr sym expr


evaluateGroundExpr ::
  (FuzzConstraints st, MonadIO m, MonadFail m) =>
  ExprBuilder t st fs ->
  Expr t tp ->
  m [(GroundValue tp, PM.MapF (Nonce t) (TypedWrapper GroundValueWrapper))]
evaluateGroundExpr sym expr =
  flip evalStateT (Random.mkStdGen ?seed) $
  replicateM ?rounds $ do
    idx_cache <- newIdxCache
    let ?cache = idx_cache

    val <- evalGroundExprStep sym expr
    cache_map <- getIdxCache ?cache

    return (val, cache_map)

evalGroundExprStep ::
  (FuzzConstraints st, MonadIO m, MonadFail m, ?cache :: IdxCache t (TypedWrapper GroundValueWrapper)) =>
  ExprBuilder t st fs ->
  Expr t tp ->
  StateT Random.StdGen m (GroundValue tp)
evalGroundExprStep sym = cacheEvalGroundExprTyped $ \e ->
  if| BoundVarExpr{} <- e ->
      randomGroundValue (exprType e)
    | Just (FnApp fn args) <- asNonceApp e -> do
      ground_args <- traverseFC (\arg -> mkGroundExpr sym (exprType arg) =<< evalGroundExprStep sym arg) args
      ground_fn_app <- liftIO $ applySymFn sym fn ground_args
      fmap (unGVW . unwrapTyped) $ idxCacheEval ?cache ground_fn_app $ fmap (TypedWrapper (exprType e) . GVW) $ do
        randomGroundValue (exprType e)
    | not ?fail ->
      randomGroundValue (exprType e)
    | otherwise ->
      fail $ "What4.Expr.Fuzz.evalGroundExprStep: unexpected expression: " ++ show e


simplifyExpr ::
  (MonadIO m, MonadFail m) =>
  ExprBuilder t st fs ->
  Expr t tp ->
  m (Expr t tp, PM.MapF (Expr t) (Expr t))
simplifyExpr = simplifyExprWithOptions defaultFuzzOptions

simplifyExprWithOptions ::
  (MonadIO m, MonadFail m) =>
  FuzzOptions st ->
  ExprBuilder t st fs ->
  Expr t tp ->
  m (Expr t tp, PM.MapF (Expr t) (Expr t))
simplifyExprWithOptions opts = withFuzzConstraints opts simplifyExprRec

simplifyExprRec ::
  (FuzzConstraints st, MonadIO m, MonadFail m) =>
  ExprBuilder t st fs ->
  Expr t tp ->
  m (Expr t tp, PM.MapF (Expr t) (Expr t))
simplifyExprRec sym expr = do
  subst <- getEquivalenceClasses sym expr
  if PM.size subst /= 0 then do
    (expr', subst') <- simplifyExprRec sym =<< applySubstitution sym subst expr
    return (expr', PM.union subst subst')
  else
    return (expr, PM.empty)


getEquivalenceClasses ::
  forall t st fs tp m .
  (FuzzConstraints st, MonadIO m, MonadFail m) =>
  ExprBuilder t st fs ->
  Expr t tp ->
  m (PM.MapF (Expr t) (Expr t))
getEquivalenceClasses sym expr = do
  candidates <- getEquivalenceClassesCandidates sym expr

  _ <- liftIO $ do
    tryExtendConfig z3Options (getConfiguration sym)
    z3TimeoutSetting <- getOptionSetting z3Timeout $ getConfiguration sym
    setOpt z3TimeoutSetting 600000
    tryExtendConfig cvc5Options (getConfiguration sym)
    cvc5TimeoutSetting <- getOptionSetting cvc5Timeout $ getConfiguration sym
    setOpt cvc5TimeoutSetting 600000

  liftIO $ solver_adapter_with_online_solver ?adapter sym Nothing $ \session -> do
    foldlM (findFoo sym session) PM.empty $ List.sortBy (\(PM.Pair e1 _) (PM.Pair e2 _) -> toOrdering $ compareClassExprF e1 e2) $ PM.toList candidates

findFoo ::
  (FuzzConstraints st, SMTReadWriter a, MonadIO m) =>
  ExprBuilder t st fs ->
  SolverProcess t a ->
  PM.MapF (Expr t) (Expr t) ->
  PM.Pair (Expr t) (TypedWrapper (SetF (Expr t))) ->
  m (PM.MapF (Expr t) (Expr t))
findFoo sym session subst (PM.Pair expr (TypedWrapper _tp (SetF exprs)))
  | disjointExprNonces expr (Set.fromList $ PM.keys subst) = do
    let foo = List.sortBy compareClassExpr $ filter (\e -> LT == compareClassExpr e expr) $ filter (\e -> PM.notMember e subst) $ Set.toList exprs
    unless (null foo) $ liftIO $ do
      putStrLn $ "getEquivalenceClasses: class expr sizes=" ++ show (map exprSize $ expr : foo)
    --   putStrLn $ "findFoo: size(subst)=" ++ show (PM.size subst) ++ ", length(class)=" ++ show (length foo) ++ ", (map exprSize class)=" ++ show (map exprSize foo)
    --   -- putStrLn $ "findFoo: expr=" ++ show expr
    res <- liftIO $ findM
      (\e -> do
        -- p <- (notPred sym <=< isEq sym expr) e
        -- putStrLn $ "findFoo: (expr=/=e)=" ++ show p
        (fmap isUnsat . checkSatisfiable session "" <=< notPred sym <=< isEq sym expr) e)
      foo
    case res of
      Just class_expr ->
        if ?variableAbstraction then do
          class_expr' <- applySubstitution sym subst class_expr
          case PM.lookup class_expr' subst of
            Just class_expr'' -> return $ PM.insert expr class_expr'' subst
            Nothing -> do
              foo <- liftIO $ freshConstant sym (safeSymbol "foo") (exprType expr)
              -- return $ PM.insert expr foo $ PM.insert class_expr' foo subst
              let bar = PM.insert expr foo $ PM.insert class_expr' foo subst
              liftIO $ putStrLn $ "getEquivalenceClasses: subst size=" ++ show (PM.size bar `div` 2)
              return bar
        else
          return $ PM.insert expr class_expr subst
      Nothing -> return subst

  | otherwise = return subst


compareClassExprF :: Expr t tp1 -> Expr t tp2 -> OrderingF tp1 tp2
compareClassExprF e1 e2 = case compare (exprSize e1) (exprSize e2) of
  LT -> LTF
  EQ -> compareF e1 e2
  GT -> GTF

compareClassExpr :: Expr t tp -> Expr t tp -> Ordering
compareClassExpr e1 e2 = toOrdering $ compareClassExprF e1 e2


getEquivalenceClassesCandidates ::
  (FuzzConstraints st, MonadIO m, MonadFail m) =>
  ExprBuilder t st fs ->
  Expr t tp ->
  m (PM.MapF (Expr t) (TypedWrapper (SetF (Expr t))))
getEquivalenceClassesCandidates sym expr = do
  foos <- map (fmapF (\x -> TypedWrapper (baseTypeRepr x) $! ListF $ List.singleton x) . snd) <$> evaluateGroundExpr sym expr
  bar <- case  foos of
    hd : tl -> do
      return $! foldl' unionMultimap hd tl
    [] -> fail $ "getEquivalenceClassesCandidates: empty key_equiv_classes, rounds = " ++ show ?rounds

  nonce_expr_tbl <- getNonceExprTable expr
  foobar <- PM.fromList <$> mapM (\(PM.Pair n s) -> do
      e <- fromMaybe (panic "getEquivalenceClassesCandidates" ["nonce not found"]) <$> liftIO (stToIO $ PH.lookup nonce_expr_tbl n)
      return $! Pair e s
    ) (PM.toList bar)

  return $! keyEquivalenceClasses foobar


newtype ListF (e :: k -> Type) (tp :: k) = ListF [e tp]
  deriving (Eq, Ord, Semigroup, Monoid, Show)

instance (forall tp . Eq (ListF e tp)) => TypedEq (ListF e)
instance (forall tp . Ord (ListF e tp)) => TypedOrd (ListF e)
instance (forall tp . Semigroup (ListF e tp)) => TypedSemigroup (ListF e)
instance (forall tp . Monoid (ListF e tp)) => TypedMonoid (ListF e)
instance (forall tp . Show (ListF e tp)) => TypedShow (ListF e)
instance FunctorFC ListF where
  fmapFC f (ListF l) = ListF $ fmap f l
instance FoldableFC ListF where
  foldMapFC f (ListF l) = foldMap f l
instance TraversableFC ListF where
  traverseFC f (ListF l) = ListF <$> traverse f l

newtype SetF (e :: k -> Type) (tp :: k) = SetF (Set (e tp))
  deriving (Eq, Ord, Semigroup, Monoid, Show)

instance (forall tp . Eq (SetF e tp)) => TypedEq (SetF e)
instance (forall tp . Ord (SetF e tp)) => TypedOrd (SetF e)
instance (forall tp . Semigroup (SetF e tp)) => TypedSemigroup (SetF e)
instance (forall tp . Monoid (SetF e tp)) => TypedMonoid (SetF e)
instance (forall tp . Show (SetF e tp)) => TypedShow (SetF e)
instance FoldableFC SetF where
  foldMapFC f (SetF s) = foldMap f s

unionMultimap ::
  (OrdF k, forall tp . Semigroup (v tp)) =>
  PM.MapF k v ->
  PM.MapF k v ->
  PM.MapF k v
unionMultimap = PM.mergeWithKey (\_ x y -> Just $! x <> y) id id


keyEquivalenceClasses ::
  (forall tp . Ord (k tp), OrdF k, OrdF v, IsTyped v) =>
  PM.MapF k v ->
  PM.MapF k (TypedWrapper (SetF k))
keyEquivalenceClasses m = PM.mapMaybe (\v -> PM.lookup v (reverseMap m)) m

reverseMap ::
  (forall tp . Ord (k tp), OrdF v, IsTyped v) =>
  PM.MapF k v ->
  PM.MapF v (TypedWrapper (SetF k))
reverseMap =
  PM.foldrWithKey'
    (\k v ->
      PM.insertWith (<>) v $! TypedWrapper (baseTypeRepr v) $! SetF $! Set.singleton k)
    PM.empty

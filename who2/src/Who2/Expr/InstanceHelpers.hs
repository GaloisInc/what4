{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

-- | Helper functions for implementing TestEquality and OrdF instances
module Who2.Expr.InstanceHelpers
  ( viaEq
  , viaEqBy
  , viaOrd
  , viaOrdBy
  , testEq
  ) where

import Data.Type.Equality (type (:~:)(Refl))
import qualified Data.Parameterized.Classes as PC

-- | Implement TestEquality via Eq
viaEq ::
  Eq a =>
  a ->
  a ->
  Maybe (b :~: b)
viaEq x y = if x == y then Just Refl else Nothing
{-# INLINE viaEq #-}

-- | Implement TestEquality via a custom equality function (like liftEq)
viaEqBy ::
  PC.TestEquality f =>
  ((f x -> f x -> Bool) -> g f -> g f -> Bool) ->
  g f ->
  g f ->
  Maybe (b :~: b)
viaEqBy eqBy x y = if eqBy testEq x y then Just Refl else Nothing
{-# INLINE viaEqBy #-}

-- | Implement OrdF via Ord
viaOrd ::
  Ord a =>
  a ->
  a ->
  PC.OrderingF b b
viaOrd x y = PC.fromOrdering (compare x y)
{-# INLINE viaOrd #-}

-- | Implement OrdF via a custom comparison function (like liftCompare)
viaOrdBy ::
  PC.OrdF f =>
  ((f x -> f y -> Ordering) -> a -> b -> Ordering) ->
  a ->
  b ->
  PC.OrderingF c c
viaOrdBy cmp x y =
  PC.fromOrdering (cmp (\u v -> PC.toOrdering (PC.compareF u v)) x y)
{-# INLINE viaOrdBy #-}

-- | Helper for comparing with TestEquality
testEq :: PC.TestEquality f => f x -> f x -> Bool
testEq u v = PC.isJust (PC.testEquality u v)
{-# INLINE testEq #-}

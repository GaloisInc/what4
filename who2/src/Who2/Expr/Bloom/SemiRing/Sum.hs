{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Sums over semirings using BloomKv for efficient small maps
module Who2.Expr.Bloom.SemiRing.Sum
  ( SRSum(..)
  , eqBy
  , eqBy2
  , ordBy
  , ordBy2
  , hashWith
  , constant
  , var
  , scaledVar
  , affineVar
  , asConstant
  , asVar
  , asWeightedVar
  , add
  , addVar
  , addConstant
  , fromTerms
  , toTerms
  , isZero
  ) where

import Data.Hashable (Hashable(hash, hashWithSalt))
import Data.Kind (Type)

import qualified What4.SemiRing as SR
import qualified What4.BaseTypes as BT

import qualified Who2.Expr.Bloom.Map as BKv

------------------------------------------------------------------------
-- Type and instances
------------------------------------------------------------------------

-- | A sum of semiring values using BloomKv.
--
-- Represents: offset + sum_i (coeff_i * term_i)
--
-- INVARIANT: Coefficients should not be zero (maintained by smart constructors)
data SRSum (sr :: SR.SemiRing) (f :: BT.BaseType -> Type) = SRSum
  { sumMap :: !(BKv.BloomKv (f (SR.SemiRingBase sr)) (SR.Coefficient sr))
    -- ^ Map from terms to their coefficients
  , sumOffset :: !(SR.Coefficient sr)
    -- ^ Constant offset
  , sumRepr :: !(SR.SemiRingRepr sr)
    -- ^ Runtime representation of the semiring
  }

-- Note: Manual Show instance to avoid needing Show for SemiRingRepr
instance (Show (f (SR.SemiRingBase sr)), Show (SR.Coefficient sr)) => Show (SRSum sr f) where
  show ws = "SRSum { sumMap = " ++ show (sumMap ws) ++
            ", sumOffset = " ++ show (sumOffset ws) ++ " }"

eqBy2 ::
  (SR.Coefficient sr -> SR.Coefficient sr -> Bool) ->
  (f (SR.SemiRingBase sr) -> f (SR.SemiRingBase sr) -> Bool) ->
  SRSum sr f ->
  SRSum sr f ->
  Bool
eqBy2 eqCoeff eqTerm x y =
  eqCoeff (sumOffset x) (sumOffset y)
  && BKv.eqBy2 eqTerm eqCoeff (sumMap x) (sumMap y)
{-# INLINE eqBy2 #-}

-- | Like 'liftEq', but without typeclass constraints (uses SR.eq for coefficient comparison)
eqBy ::
  (f (SR.SemiRingBase sr) -> f (SR.SemiRingBase sr) -> Bool) ->
  SRSum sr f ->
  SRSum sr f ->
  Bool
eqBy eqTerm x y = eqBy2 (SR.eq (sumRepr x)) eqTerm x y
{-# INLINE eqBy #-}

-- | @'eqBy' (==)@
instance Eq (f (SR.SemiRingBase sr)) => Eq (SRSum sr f) where
  x == y = eqBy (==) x y

ordBy2 ::
  (SR.Coefficient sr -> SR.Coefficient sr -> Ordering) ->
  (f (SR.SemiRingBase sr) -> f (SR.SemiRingBase sr) -> Ordering) ->
  SRSum sr f ->
  SRSum sr f ->
  Ordering
ordBy2 cmpCoeff cmpTerm x y =
  case cmpCoeff (sumOffset x) (sumOffset y) of
    EQ -> BKv.ordBy2 cmpTerm cmpCoeff (sumMap x) (sumMap y)
    c -> c
{-# INLINE ordBy2 #-}

-- | Like 'liftCompare', but without typeclass constraints (uses SR.compare for coefficient comparison)
ordBy ::
  (f (SR.SemiRingBase sr) -> f (SR.SemiRingBase sr) -> Ordering) ->
  SRSum sr f ->
  SRSum sr f ->
  Ordering
ordBy cmpTerm x y = ordBy2 (SR.sr_compare (sumRepr x)) cmpTerm x y
{-# INLINE ordBy #-}

-- | @'ordBy' 'compare'@
instance
  ( Ord (f (SR.SemiRingBase sr))
  , Ord (SR.Coefficient sr)
  ) => Ord (SRSum sr f) where
  compare = ordBy compare

hashWith ::
  Hashable (SR.Coefficient sr) =>
  (BKv.BloomKv (f (SR.SemiRingBase sr)) (SR.Coefficient sr) -> Int) ->
  Int ->
  SRSum sr f ->
  Int
hashWith hashMap salt x =
  hashMap (sumMap x) `hashWithSalt` salt `hashWithSalt` sumOffset x
{-# INLINE hashWith #-}

instance
  ( Hashable (f (SR.SemiRingBase sr))
  , Hashable (SR.Coefficient sr)
  ) => Hashable (SRSum sr f) where
  hash ws = hash (sumOffset ws) `hashWithSalt` hash (sumMap ws)
  {-# INLINE hash #-}
  hashWithSalt salt = hashWith hash salt
  {-# INLINE hashWithSalt #-}

------------------------------------------------------------------------
-- Operations
------------------------------------------------------------------------

-- | Create a constant sum
constant :: SR.SemiRingRepr sr -> SR.Coefficient sr -> SRSum sr f
constant sr c = SRSum BKv.empty c sr

-- | Create a sum from a single variable
var :: (Eq (f (SR.SemiRingBase sr)), Hashable (f (SR.SemiRingBase sr)), Hashable (SR.Coefficient sr)) =>
       SR.SemiRingRepr sr -> f (SR.SemiRingBase sr) -> SRSum sr f
var sr x = SRSum (BKv.singleton x (SR.one sr)) (SR.zero sr) sr

-- | Create a sum from a scaled variable with offset: @coeff * var + offset@
affineVar ::
  (Eq (f (SR.SemiRingBase sr)), Hashable (f (SR.SemiRingBase sr)), Hashable (SR.Coefficient sr)) =>
  SR.SemiRingRepr sr ->
  SR.Coefficient sr ->  -- ^ Coefficient
  f (SR.SemiRingBase sr) ->  -- ^ Variable
  SR.Coefficient sr ->  -- ^ Offset
  SRSum sr f
affineVar sr coeff x offset
  | SR.eq sr coeff (SR.zero sr) = constant sr offset
  | otherwise = SRSum (BKv.singleton x coeff) offset sr

-- | Create a sum from a scaled variable: @coeff * var@
scaledVar ::
  (Eq (f (SR.SemiRingBase sr)), Hashable (f (SR.SemiRingBase sr)), Hashable (SR.Coefficient sr)) =>
  SR.SemiRingRepr sr ->
  SR.Coefficient sr ->
  f (SR.SemiRingBase sr) ->
  SRSum sr f
scaledVar sr coeff x = affineVar sr coeff x (SR.zero sr)

-- | Check if the sum is a constant
asConstant :: SRSum sr f -> Maybe (SR.Coefficient sr)
asConstant ws
  | BKv.isEmpty (sumMap ws) = Just (sumOffset ws)
  | otherwise = Nothing

-- | Check if the sum is a single unscaled variable (with possible offset)
asVar :: SRSum sr f -> Maybe (f (SR.SemiRingBase sr), SR.Coefficient sr)
asVar ws
  | [(x, c)] <- BKv.toList (sumMap ws)
  , SR.eq (sumRepr ws) c (SR.one (sumRepr ws))
  = Just (x, sumOffset ws)
  | otherwise = Nothing

-- | Check if the sum is a single scaled variable (with possible offset)
asWeightedVar ::
  SRSum sr f ->
  Maybe (SR.Coefficient sr, f (SR.SemiRingBase sr), SR.Coefficient sr)
asWeightedVar ws
  | [(x, c)] <- BKv.toList (sumMap ws) = Just (c, x, sumOffset ws)
  | otherwise = Nothing

-- | Check if the sum is zero
isZero :: SRSum sr f -> Bool
isZero ws =
  BKv.isEmpty (sumMap ws) && SR.eq (sumRepr ws) (sumOffset ws) (SR.zero (sumRepr ws))

-- | Add two sums
add ::
  (Eq (f (SR.SemiRingBase sr)), Ord (f (SR.SemiRingBase sr)), Hashable (f (SR.SemiRingBase sr)), Hashable (SR.Coefficient sr)) =>
  SRSum sr f ->
  SRSum sr f ->
  SRSum sr f
add ws1 ws2 =
  SRSum
    (BKv.merge (SR.add sr) (sumMap ws1) (sumMap ws2))
    (SR.add sr (sumOffset ws1) (sumOffset ws2))
    sr
  where sr = sumRepr ws1

-- | Add a variable with coefficient 1 to a sum
addVar ::
  (Eq (f (SR.SemiRingBase sr)), Hashable (f (SR.SemiRingBase sr)), Hashable (SR.Coefficient sr)) =>
  SRSum sr f ->
  f (SR.SemiRingBase sr) ->
  SRSum sr f
addVar ws x =
  SRSum
    (BKv.insert (SR.add sr) (sumMap ws) x (SR.one sr))
    (sumOffset ws)
    sr
  where sr = sumRepr ws

-- | Add a constant to a sum
addConstant :: SRSum sr f -> SR.Coefficient sr -> SRSum sr f
addConstant ws c =
  ws { sumOffset = SR.add (sumRepr ws) (sumOffset ws) c }

-- | Create a sum from a list of terms and an offset
fromTerms ::
  (Eq (f (SR.SemiRingBase sr)), Hashable (f (SR.SemiRingBase sr)), Hashable (SR.Coefficient sr)) =>
  SR.SemiRingRepr sr ->
  [(f (SR.SemiRingBase sr), SR.Coefficient sr)] ->
  SR.Coefficient sr ->
  SRSum sr f
fromTerms sr terms offset =
  SRSum
    (BKv.fromList (SR.add sr) terms)
    offset
    sr

-- | Convert a sum to a list of terms
toTerms :: SRSum sr f -> [(f (SR.SemiRingBase sr), SR.Coefficient sr)]
toTerms = BKv.toList . sumMap

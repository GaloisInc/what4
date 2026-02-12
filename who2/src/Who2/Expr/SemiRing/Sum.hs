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
module Who2.Expr.SemiRing.Sum
  ( SRSum(..)
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

import qualified Prelude as P
import Prelude (Eq((==)), Ord(compare), Show(show), Bool, Maybe(Just, Nothing), (.), otherwise)
import Data.Hashable (Hashable(hash, hashWithSalt))
import Data.Bits (xor)
import qualified Data.Parameterized.Classes as PC

import qualified What4.SemiRing as SR

import qualified Who2.Expr.BloomKv as BKv

-- | A sum of semiring values using BloomKv.
--
-- Represents: offset + sum_i (coeff_i * term_i)
--
-- INVARIANT: Coefficients should not be zero (maintained by smart constructors)
data SRSum (sr :: SR.SemiRing) f = SRSum
  { sumMap :: !(BKv.BloomKv (f (SR.SemiRingBase sr)) (SR.Coefficient sr))
    -- ^ Map from terms to their coefficients
  , sumOffset :: !(SR.Coefficient sr)
    -- ^ Constant offset
  , sumRepr :: !(SR.SemiRingRepr sr)
    -- ^ Runtime representation of the semiring
  }

-- Note: Manual Show instance to avoid needing Show for SemiRingRepr
instance (Show (f (SR.SemiRingBase sr)), Show (SR.Coefficient sr)) => Show (SRSum sr f) where
  show ws = "SRSum { sumMap = " P.++ P.show (sumMap ws) P.++
            ", sumOffset = " P.++ P.show (sumOffset ws) P.++ " }"

instance
  ( PC.TestEquality f
  , Eq (f (SR.SemiRingBase sr))
  , Hashable (f (SR.SemiRingBase sr))
  , Hashable (SR.Coefficient sr)
  ) => Eq (SRSum sr f) where
  ws1 == ws2 =
    SR.eq (sumRepr ws1) (sumOffset ws1) (sumOffset ws2)
    P.&& BKv.eqBy (==) (SR.eq (sumRepr ws1)) (sumMap ws1) (sumMap ws2)

instance
  ( PC.TestEquality f
  , Ord (f (SR.SemiRingBase sr))
  , Ord (SR.Coefficient sr)
  , Hashable (f (SR.SemiRingBase sr))
  , Hashable (SR.Coefficient sr)
  ) => Ord (SRSum sr f) where
  compare ws1 ws2 =
    case P.compare (sumOffset ws1) (sumOffset ws2) of
      P.EQ -> BKv.ordBy compare (SR.sr_compare (sumRepr ws1)) (sumMap ws1) (sumMap ws2)
      c -> c

instance
  ( PC.TestEquality f
  , PC.HashableF f
  , Hashable (f (SR.SemiRingBase sr))
  , Hashable (SR.Coefficient sr)
  ) => Hashable (SRSum sr f) where
  hash ws = hash (sumOffset ws) `hashWithSalt` hash (sumMap ws)
  hashWithSalt salt ws = salt `xor` hash ws

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
  BKv.isEmpty (sumMap ws) P.&& SR.eq (sumRepr ws) (sumOffset ws) (SR.zero (sumRepr ws))

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

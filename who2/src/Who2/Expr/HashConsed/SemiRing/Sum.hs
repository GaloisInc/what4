{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Who2.Expr.HashConsed.SemiRing.Sum
  ( SRSum(..)
  , eqBy
  , eqBy2
  , ordBy
  , ordBy2
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
  , sumOffset
  , sumRepr
  ) where

import Data.Hashable (Hashable(hashWithSalt))
import Data.Kind (Type)

import qualified What4.SemiRing as SR
import qualified What4.BaseTypes as BT

import qualified Who2.Expr.HashConsed.ExprMap as EM
import Who2.Expr (HasId)

------------------------------------------------------------------------
-- Type and instances
------------------------------------------------------------------------

-- | A hash-consed sum of semiring values using ExprMap.
data SRSum (sr :: SR.SemiRing) (f :: BT.BaseType -> Type) = SRSum
  { sumMap :: !(EM.ExprMap (f (SR.SemiRingBase sr)) (SR.Coefficient sr))
  , sumOffsetHC :: !(SR.Coefficient sr)
  , sumReprHC :: !(SR.SemiRingRepr sr)
  }

eqBy2 ::
  (SR.Coefficient sr -> SR.Coefficient sr -> Bool) ->
  (f (SR.SemiRingBase sr) -> f (SR.SemiRingBase sr) -> Bool) ->
  SRSum sr f ->
  SRSum sr f ->
  Bool
eqBy2 eqCoeff eqTerm ws1 ws2 =
  eqCoeff (sumOffset ws1) (sumOffset ws2)
  && EM.eqBy2 eqTerm eqCoeff (sumMap ws1) (sumMap ws2)
{-# INLINE eqBy2 #-}

-- | Like 'liftEq', but without typeclass constraints (uses SR.eq for coefficient comparison)
eqBy ::
  (f (SR.SemiRingBase sr) -> f (SR.SemiRingBase sr) -> Bool) ->
  SRSum sr f ->
  SRSum sr f ->
  Bool
eqBy eqTerm ws1 ws2 = eqBy2 (SR.eq (sumRepr ws1)) eqTerm ws1 ws2
{-# INLINE eqBy #-}

-- | @'eqBy' (==)@
instance Eq (f (SR.SemiRingBase sr)) => Eq (SRSum sr f) where
  ws1 == ws2 = eqBy (==) ws1 ws2
  {-# INLINE (==) #-}

ordBy2 ::
  (SR.Coefficient sr -> SR.Coefficient sr -> Ordering) ->
  (f (SR.SemiRingBase sr) -> f (SR.SemiRingBase sr) -> Ordering) ->
  SRSum sr f ->
  SRSum sr f ->
  Ordering
ordBy2 cmpCoeff cmpTerm ws1 ws2 =
  case cmpCoeff (sumOffset ws1) (sumOffset ws2) of
    EQ -> EM.ordBy2 cmpTerm cmpCoeff (sumMap ws1) (sumMap ws2)
    c -> c
{-# INLINE ordBy2 #-}

-- | Like 'liftCompare', but without typeclass constraints (uses SR.compare for coefficient comparison)
ordBy ::
  (f (SR.SemiRingBase sr) -> f (SR.SemiRingBase sr) -> Ordering) ->
  SRSum sr f ->
  SRSum sr f ->
  Ordering
ordBy cmpTerm ws1 ws2 = ordBy2 (SR.sr_compare (sumRepr ws1)) cmpTerm ws1 ws2
{-# INLINE ordBy #-}

-- | @'ordBy' 'compare'@
instance
  ( Ord (f (SR.SemiRingBase sr))
  , Ord (SR.Coefficient sr)
  ) => Ord (SRSum sr f) where
  compare = ordBy compare
  {-# INLINE compare #-}

instance
  ( Hashable (f (SR.SemiRingBase sr))
  , Hashable (SR.Coefficient sr)
  ) => Hashable (SRSum sr f) where
  hashWithSalt salt ws =
    salt `hashWithSalt` sumOffset ws `hashWithSalt` sumMap ws

------------------------------------------------------------------------
-- Operations
------------------------------------------------------------------------

sumOffset :: SRSum sr f -> SR.Coefficient sr
sumOffset = sumOffsetHC
{-# INLINE sumOffset #-}

sumRepr :: SRSum sr f -> SR.SemiRingRepr sr
sumRepr = sumReprHC
{-# INLINE sumRepr #-}

constant :: SR.SemiRingRepr sr -> SR.Coefficient sr -> SRSum sr f
constant sr c = SRSum EM.empty c sr
{-# INLINE constant #-}

var :: HasId (f (SR.SemiRingBase sr)) => SR.SemiRingRepr sr -> f (SR.SemiRingBase sr) -> SRSum sr f
var sr x = SRSum (EM.singleton x (SR.one sr)) (SR.zero sr) sr
{-# INLINE var #-}

affineVar ::
  HasId (f (SR.SemiRingBase sr)) =>
  SR.SemiRingRepr sr ->
  SR.Coefficient sr ->
  f (SR.SemiRingBase sr) ->
  SR.Coefficient sr ->
  SRSum sr f
affineVar sr coeff x offset
  | SR.eq sr coeff (SR.zero sr) = constant sr offset
  | otherwise = SRSum (EM.singleton x coeff) offset sr
{-# INLINE affineVar #-}

scaledVar ::
  HasId (f (SR.SemiRingBase sr)) =>
  SR.SemiRingRepr sr ->
  SR.Coefficient sr ->
  f (SR.SemiRingBase sr) ->
  SRSum sr f
scaledVar sr coeff x = affineVar sr coeff x (SR.zero sr)
{-# INLINE scaledVar #-}

asConstant :: SRSum sr f -> Maybe (SR.Coefficient sr)
asConstant ws
  | EM.size (sumMap ws) == 0 = Just (sumOffsetHC ws)
  | otherwise = Nothing
{-# INLINE asConstant #-}

asVar :: SRSum sr f -> Maybe (f (SR.SemiRingBase sr), SR.Coefficient sr)
asVar ws
  | [(x, c)] <- EM.toList (sumMap ws)
  , SR.eq (sumReprHC ws) c (SR.one (sumReprHC ws))
  = Just (x, sumOffsetHC ws)
  | otherwise = Nothing
{-# INLINE asVar #-}

asWeightedVar ::
  SRSum sr f ->
  Maybe (SR.Coefficient sr, f (SR.SemiRingBase sr), SR.Coefficient sr)
asWeightedVar ws
  | [(x, c)] <- EM.toList (sumMap ws) = Just (c, x, sumOffsetHC ws)
  | otherwise = Nothing
{-# INLINE asWeightedVar #-}

isZero :: SRSum sr f -> Bool
isZero ws =
  EM.size (sumMap ws) == 0 && SR.eq (sumReprHC ws) (sumOffsetHC ws) (SR.zero (sumReprHC ws))
{-# INLINE isZero #-}

add :: SRSum sr f -> SRSum sr f -> SRSum sr f
add ws1 ws2 =
  SRSum
    (EM.unionWith (SR.add sr) (sumMap ws1) (sumMap ws2))
    (SR.add sr (sumOffsetHC ws1) (sumOffsetHC ws2))
    sr
  where sr = sumReprHC ws1
{-# INLINE add #-}

addVar :: HasId (f (SR.SemiRingBase sr)) => SRSum sr f -> f (SR.SemiRingBase sr) -> SRSum sr f
addVar ws x =
  SRSum
    (EM.insertWith (SR.add sr) x (SR.one sr) (sumMap ws))
    (sumOffsetHC ws)
    sr
  where sr = sumReprHC ws
{-# INLINE addVar #-}

addConstant :: SRSum sr f -> SR.Coefficient sr -> SRSum sr f
addConstant ws c =
  ws { sumOffsetHC = SR.add (sumReprHC ws) (sumOffsetHC ws) c }
{-# INLINE addConstant #-}

fromTerms ::
  HasId (f (SR.SemiRingBase sr)) =>
  SR.SemiRingRepr sr ->
  [(f (SR.SemiRingBase sr), SR.Coefficient sr)] ->
  SR.Coefficient sr ->
  SRSum sr f
fromTerms sr terms offset =
  SRSum
    (foldr (\(k, v) m -> EM.insertWith (SR.add sr) k v m) EM.empty terms)
    offset
    sr
{-# INLINE fromTerms #-}

toTerms :: SRSum sr f -> [(f (SR.SemiRingBase sr), SR.Coefficient sr)]
toTerms = EM.toList . sumMap
{-# INLINE toTerms #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

module Who2.Expr.HashConsed.SRSum
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
  , sumOffset
  , sumRepr
  ) where

import qualified Prelude as P
import Prelude (Bool, Maybe(Just, Nothing), (.), otherwise)
import Data.Kind (Type)

import qualified What4.SemiRing as SR
import qualified What4.BaseTypes as BT

import qualified Who2.Expr.HashConsed.ExprMap as EM
import Who2.Expr (HasNonce)

-- | A hash-consed sum of semiring values using ExprMap.
data SRSum (sr :: SR.SemiRing) (f :: BT.BaseType -> Type) = SRSum
  { sumMapHC :: !(EM.ExprMap f (SR.SemiRingBase sr) (SR.Coefficient sr))
  , sumOffsetHC :: !(SR.Coefficient sr)
  , sumReprHC :: !(SR.SemiRingRepr sr)
  }

sumOffset :: SRSum sr f -> SR.Coefficient sr
sumOffset = sumOffsetHC
{-# INLINE sumOffset #-}

sumRepr :: SRSum sr f -> SR.SemiRingRepr sr
sumRepr = sumReprHC
{-# INLINE sumRepr #-}

constant :: SR.SemiRingRepr sr -> SR.Coefficient sr -> SRSum sr f
constant sr c = SRSum EM.empty c sr
{-# INLINE constant #-}

var :: HasNonce f => SR.SemiRingRepr sr -> f (SR.SemiRingBase sr) -> SRSum sr f
var sr x = SRSum (EM.singleton x (SR.one sr)) (SR.zero sr) sr
{-# INLINE var #-}

affineVar ::
  HasNonce f =>
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
  HasNonce f =>
  SR.SemiRingRepr sr ->
  SR.Coefficient sr ->
  f (SR.SemiRingBase sr) ->
  SRSum sr f
scaledVar sr coeff x = affineVar sr coeff x (SR.zero sr)
{-# INLINE scaledVar #-}

asConstant :: SRSum sr f -> Maybe (SR.Coefficient sr)
asConstant ws
  | EM.size (sumMapHC ws) P.== 0 = Just (sumOffsetHC ws)
  | otherwise = Nothing
{-# INLINE asConstant #-}

asVar :: SRSum sr f -> Maybe (f (SR.SemiRingBase sr), SR.Coefficient sr)
asVar ws
  | [(x, c)] <- EM.toList (sumMapHC ws)
  , SR.eq (sumReprHC ws) c (SR.one (sumReprHC ws))
  = Just (x, sumOffsetHC ws)
  | otherwise = Nothing
{-# INLINE asVar #-}

asWeightedVar ::
  SRSum sr f ->
  Maybe (SR.Coefficient sr, f (SR.SemiRingBase sr), SR.Coefficient sr)
asWeightedVar ws
  | [(x, c)] <- EM.toList (sumMapHC ws) = Just (c, x, sumOffsetHC ws)
  | otherwise = Nothing
{-# INLINE asWeightedVar #-}

isZero :: SRSum sr f -> Bool
isZero ws =
  EM.size (sumMapHC ws) P.== 0 P.&& SR.eq (sumReprHC ws) (sumOffsetHC ws) (SR.zero (sumReprHC ws))
{-# INLINE isZero #-}

add :: SRSum sr f -> SRSum sr f -> SRSum sr f
add ws1 ws2 =
  SRSum
    (EM.unionWith (SR.add sr) (sumMapHC ws1) (sumMapHC ws2))
    (SR.add sr (sumOffsetHC ws1) (sumOffsetHC ws2))
    sr
  where sr = sumReprHC ws1
{-# INLINE add #-}

addVar :: HasNonce f => SRSum sr f -> f (SR.SemiRingBase sr) -> SRSum sr f
addVar ws x =
  SRSum
    (EM.insertWith (SR.add sr) x (SR.one sr) (sumMapHC ws))
    (sumOffsetHC ws)
    sr
  where sr = sumReprHC ws
{-# INLINE addVar #-}

addConstant :: SRSum sr f -> SR.Coefficient sr -> SRSum sr f
addConstant ws c =
  ws { sumOffsetHC = SR.add (sumReprHC ws) (sumOffsetHC ws) c }
{-# INLINE addConstant #-}

fromTerms ::
  HasNonce f =>
  SR.SemiRingRepr sr ->
  [(f (SR.SemiRingBase sr), SR.Coefficient sr)] ->
  SR.Coefficient sr ->
  SRSum sr f
fromTerms sr terms offset =
  SRSum
    (P.foldr (\(k, v) m -> EM.insertWith (SR.add sr) k v m) EM.empty terms)
    offset
    sr
{-# INLINE fromTerms #-}

toTerms :: SRSum sr f -> [(f (SR.SemiRingBase sr), SR.Coefficient sr)]
toTerms = EM.toList . sumMapHC
{-# INLINE toTerms #-}

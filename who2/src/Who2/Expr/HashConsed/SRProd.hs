{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

module Who2.Expr.HashConsed.SRProd
  ( SRProd(..)
  , constant
  , var
  , one
  , fromTerms
  , toTerms
  , mul
  , mulVar
  , scale
  , asConstant
  , asVar
  , contains
  , prodCoeff
  , prodRepr
  ) where

import qualified Prelude as P
import Prelude (Bool, Maybe(Just, Nothing), (.), otherwise)
import Data.Kind (Type)
import Numeric.Natural (Natural)

import qualified What4.SemiRing as SR
import qualified What4.BaseTypes as BT

import qualified Who2.Expr.HashConsed.ExprMap as EM
import Who2.Expr (HasNonce)

-- | A hash-consed product of semiring values using ExprMap.
data SRProd (sr :: SR.SemiRing) (f :: BT.BaseType -> Type) = SRProd
  { prodMapHC :: !(EM.ExprMap f (SR.SemiRingBase sr) Natural)
  , prodCoeffHC :: !(SR.Coefficient sr)
  , prodReprHC :: !(SR.SemiRingRepr sr)
  }

prodCoeff :: SRProd sr f -> SR.Coefficient sr
prodCoeff = prodCoeffHC
{-# INLINE prodCoeff #-}

prodRepr :: SRProd sr f -> SR.SemiRingRepr sr
prodRepr = prodReprHC
{-# INLINE prodRepr #-}

constant :: SR.SemiRingRepr sr -> SR.Coefficient sr -> SRProd sr f
constant sr c = SRProd EM.empty c sr
{-# INLINE constant #-}

one :: SR.SemiRingRepr sr -> SRProd sr f
one sr = SRProd EM.empty (SR.one sr) sr
{-# INLINE one #-}

var :: HasNonce f => SR.SemiRingRepr sr -> f (SR.SemiRingBase sr) -> SRProd sr f
var sr x = SRProd (EM.singleton x 1) (SR.one sr) sr
{-# INLINE var #-}

fromTerms ::
  HasNonce f =>
  SR.SemiRingRepr sr ->
  [(f (SR.SemiRingBase sr), Natural)] ->
  SRProd sr f
fromTerms sr terms =
  SRProd
    (P.foldr (\(k, v) m -> if v P./= 0 then EM.insertWith (P.+) k v m else m) EM.empty terms)
    (SR.one sr)
    sr
{-# INLINE fromTerms #-}

toTerms :: SRProd sr f -> [(f (SR.SemiRingBase sr), Natural)]
toTerms = EM.toList . prodMapHC
{-# INLINE toTerms #-}

mul :: SRProd sr f -> SRProd sr f -> SRProd sr f
mul p1 p2 =
  let sr = prodReprHC p1
  in SRProd
       (EM.unionWith (P.+) (prodMapHC p1) (prodMapHC p2))
       (SR.mul sr (prodCoeffHC p1) (prodCoeffHC p2))
       sr
{-# INLINE mul #-}

mulVar :: HasNonce f => SRProd sr f -> f (SR.SemiRingBase sr) -> SRProd sr f
mulVar p x =
  SRProd
    (EM.insertWith (P.+) x 1 (prodMapHC p))
    (prodCoeffHC p)
    (prodReprHC p)
{-# INLINE mulVar #-}

scale :: SRProd sr f -> SR.Coefficient sr -> SRProd sr f
scale p c =
  let sr = prodReprHC p
  in SRProd
       (prodMapHC p)
       (SR.mul sr (prodCoeffHC p) c)
       sr
{-# INLINE scale #-}

asConstant :: SRProd sr f -> Maybe (SR.Coefficient sr)
asConstant p
  | EM.size (prodMapHC p) P.== 0 = Just (prodCoeffHC p)
  | otherwise = Nothing
{-# INLINE asConstant #-}

asVar :: SRProd sr f -> Maybe (f (SR.SemiRingBase sr))
asVar p
  | [(x, e)] <- EM.toList (prodMapHC p)
  , e P.== 1
  , SR.eq (prodReprHC p) (prodCoeffHC p) (SR.one (prodReprHC p))
  = Just x
  | otherwise = Nothing
{-# INLINE asVar #-}

contains :: HasNonce f => SRProd sr f -> f (SR.SemiRingBase sr) -> Bool
contains p x =
  case EM.lookup x (prodMapHC p) of
    Just _ -> P.True
    Nothing -> P.False
{-# INLINE contains #-}

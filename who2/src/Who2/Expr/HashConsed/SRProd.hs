{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Who2.Expr.HashConsed.SRProd
  ( SRProd
  , eqBy
  , eqBy2
  , ordBy
  , ordBy2
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

import Data.Hashable (Hashable(hashWithSalt))
import Data.Kind (Type)
import Numeric.Natural (Natural)

import qualified What4.SemiRing as SR
import qualified What4.BaseTypes as BT

import qualified Who2.Expr.HashConsed.ExprMap as EM
import Who2.Expr (HasId)

------------------------------------------------------------------------
-- Type and instances
------------------------------------------------------------------------

-- | A hash-consed product of semiring values using ExprMap.
data SRProd (sr :: SR.SemiRing) (f :: BT.BaseType -> Type) = SRProd
  { prodMap :: !(EM.ExprMap (f (SR.SemiRingBase sr)) Natural)
  , prodCoeff :: !(SR.Coefficient sr)
  , prodRepr :: !(SR.SemiRingRepr sr)
  }

eqBy2 ::
  (SR.Coefficient sr -> SR.Coefficient sr -> Bool) ->
  (f (SR.SemiRingBase sr) -> f (SR.SemiRingBase sr) -> Bool) ->
  SRProd sr f ->
  SRProd sr f ->
  Bool
eqBy2 eqCoeff eqTerm p1 p2 =
  eqCoeff (prodCoeff p1) (prodCoeff p2)
  && EM.eqBy2 eqTerm (==) (prodMap p1) (prodMap p2)
{-# INLINE eqBy2 #-}

-- | Like 'liftEq', but without typeclass constraints (uses SR.eq for coefficient comparison)
eqBy ::
  (f (SR.SemiRingBase sr) -> f (SR.SemiRingBase sr) -> Bool) ->
  SRProd sr f ->
  SRProd sr f ->
  Bool
eqBy eqTerm p1 p2 = eqBy2 (SR.eq (prodRepr p1)) eqTerm p1 p2
{-# INLINE eqBy #-}

-- | @'eqBy' (==)@
instance Eq (f (SR.SemiRingBase sr)) => Eq (SRProd sr f) where
  x == y = eqBy (==) x y
  {-# INLINE (==) #-}

ordBy2 ::
  (SR.Coefficient sr -> SR.Coefficient sr -> Ordering) ->
  (f (SR.SemiRingBase sr) -> f (SR.SemiRingBase sr) -> Ordering) ->
  SRProd sr f ->
  SRProd sr f ->
  Ordering
ordBy2 cmpCoeff cmpTerm p1 p2 =
  case cmpCoeff (prodCoeff p1) (prodCoeff p2) of
    EQ -> EM.ordBy2 cmpTerm compare (prodMap p1) (prodMap p2)
    other -> other
{-# INLINE ordBy2 #-}

-- | Like 'liftCompare', but without typeclass constraints (uses SR.compare for coefficient comparison)
ordBy ::
  (f (SR.SemiRingBase sr) -> f (SR.SemiRingBase sr) -> Ordering) ->
  SRProd sr f ->
  SRProd sr f ->
  Ordering
ordBy cmpTerm p1 p2 = ordBy2 (SR.sr_compare (prodRepr p1)) cmpTerm p1 p2
{-# INLINE ordBy #-}

-- | @'ordBy' 'compare'@
instance
  ( Ord (f (SR.SemiRingBase sr))
  , Ord (SR.Coefficient sr)
  ) => Ord (SRProd sr f) where
  compare = ordBy compare
  {-# INLINE compare #-}

instance
  ( Hashable (f (SR.SemiRingBase sr))
  , Hashable (SR.Coefficient sr)
  ) => Hashable (SRProd sr f) where
  hashWithSalt salt ws =
    salt `hashWithSalt` prodCoeff ws `hashWithSalt` prodMap ws

------------------------------------------------------------------------
-- Operations
------------------------------------------------------------------------

constant :: SR.SemiRingRepr sr -> SR.Coefficient sr -> SRProd sr f
constant sr c = SRProd EM.empty c sr
{-# INLINE constant #-}

one :: SR.SemiRingRepr sr -> SRProd sr f
one sr = SRProd EM.empty (SR.one sr) sr
{-# INLINE one #-}

var :: HasId (f (SR.SemiRingBase sr)) => SR.SemiRingRepr sr -> f (SR.SemiRingBase sr) -> SRProd sr f
var sr x = SRProd (EM.singleton x 1) (SR.one sr) sr
{-# INLINE var #-}

fromTerms ::
  HasId (f (SR.SemiRingBase sr)) =>
  SR.SemiRingRepr sr ->
  [(f (SR.SemiRingBase sr), Natural)] ->
  SRProd sr f
fromTerms sr terms =
  SRProd
    (foldr (\(k, v) m -> if v /= 0 then EM.insertWith (+) k v m else m) EM.empty terms)
    (SR.one sr)
    sr
{-# INLINE fromTerms #-}

toTerms :: SRProd sr f -> [(f (SR.SemiRingBase sr), Natural)]
toTerms = EM.toList . prodMap
{-# INLINE toTerms #-}

mul :: SRProd sr f -> SRProd sr f -> SRProd sr f
mul p1 p2 =
  let sr = prodRepr p1
  in SRProd
       (EM.unionWith (+) (prodMap p1) (prodMap p2))
       (SR.mul sr (prodCoeff p1) (prodCoeff p2))
       sr
{-# INLINE mul #-}

mulVar :: HasId (f (SR.SemiRingBase sr)) => SRProd sr f -> f (SR.SemiRingBase sr) -> SRProd sr f
mulVar p x =
  SRProd
    (EM.insertWith (+) x 1 (prodMap p))
    (prodCoeff p)
    (prodRepr p)
{-# INLINE mulVar #-}

scale :: SRProd sr f -> SR.Coefficient sr -> SRProd sr f
scale p c =
  let sr = prodRepr p
  in SRProd
       (prodMap p)
       (SR.mul sr (prodCoeff p) c)
       sr
{-# INLINE scale #-}

asConstant :: SRProd sr f -> Maybe (SR.Coefficient sr)
asConstant p
  | EM.size (prodMap p) == 0 = Just (prodCoeff p)
  | otherwise = Nothing
{-# INLINE asConstant #-}

asVar :: SRProd sr f -> Maybe (f (SR.SemiRingBase sr))
asVar p
  | [(x, e)] <- EM.toList (prodMap p)
  , e == 1
  , SR.eq (prodRepr p) (prodCoeff p) (SR.one (prodRepr p))
  = Just x
  | otherwise = Nothing
{-# INLINE asVar #-}

contains :: HasId (f (SR.SemiRingBase sr)) => SRProd sr f -> f (SR.SemiRingBase sr) -> Bool
contains p x =
  case EM.lookup x (prodMap p) of
    Just _ -> True
    Nothing -> False
{-# INLINE contains #-}

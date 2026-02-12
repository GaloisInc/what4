{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Products over semirings using BloomKv for efficient small maps
module Who2.Expr.SemiRing.Product
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
  ) where

import qualified Prelude as P
import Prelude (Eq((==)), Ord(compare), Ordering(EQ), Show(show), Bool, Maybe(Just, Nothing), (.), (&&), otherwise)
import Data.Hashable (Hashable(hashWithSalt))
import Numeric.Natural (Natural)
import qualified Data.Parameterized.Classes as PC

import qualified What4.SemiRing as SR

import qualified Who2.Expr.BloomKv as BKv

-- | A product of semiring values using BloomKv.
--
-- Represents: coeff * product_i (term_i ^ exponent_i)
--
-- INVARIANT: Exponents should not be zero (maintained by smart constructors)
data SRProd (sr :: SR.SemiRing) f = SRProd
  { prodMap :: !(BKv.BloomKv (f (SR.SemiRingBase sr)) Natural)
    -- ^ Map from terms to their exponents
  , prodCoeff :: !(SR.Coefficient sr)
    -- ^ Constant coefficient
  , prodRepr :: !(SR.SemiRingRepr sr)
    -- ^ Runtime representation of the semiring
  }

-- Note: Manual Show instance to avoid needing Show for SemiRingRepr
instance (Show (f (SR.SemiRingBase sr)), Show (SR.Coefficient sr)) => Show (SRProd sr f) where
  show p = "SRProd { prodMap = " P.++ P.show (prodMap p) P.++
           ", prodCoeff = " P.++ P.show (prodCoeff p) P.++ " }"

instance (PC.TestEquality f, Eq (f (SR.SemiRingBase sr)), Eq (SR.Coefficient sr)) => Eq (SRProd sr f) where
  p1 == p2 = prodCoeff p1 == prodCoeff p2 && BKv.eqBy (==) (==) (prodMap p1) (prodMap p2)

instance (PC.TestEquality f, Ord (f (SR.SemiRingBase sr)), Ord (SR.Coefficient sr)) => Ord (SRProd sr f) where
  compare p1 p2 = case compare (prodCoeff p1) (prodCoeff p2) of
    EQ -> BKv.ordBy compare compare (prodMap p1) (prodMap p2)
    other -> other

instance (PC.TestEquality f, PC.HashableF f, Hashable (f (SR.SemiRingBase sr)), Hashable (SR.Coefficient sr)) => Hashable (SRProd sr f) where
  hashWithSalt s p = hashWithSalt (hashWithSalt s (prodCoeff p)) (prodMap p)

-- | Create a constant product
constant :: SR.SemiRingRepr sr -> SR.Coefficient sr -> SRProd sr f
constant sr c = SRProd BKv.empty c sr

-- | Create the multiplicative identity (empty product with coefficient 1)
one :: SR.SemiRingRepr sr -> SRProd sr f
one sr = SRProd BKv.empty (SR.one sr) sr

-- | Create a product from a single variable (coefficient 1)
var :: (Eq (f (SR.SemiRingBase sr)), Hashable (f (SR.SemiRingBase sr))) =>
       SR.SemiRingRepr sr -> f (SR.SemiRingBase sr) -> SRProd sr f
var sr x = SRProd (BKv.singleton x 1) (SR.one sr) sr

-- | Create a product from a list of terms and their exponents (coefficient 1)
fromTerms ::
  (Eq (f (SR.SemiRingBase sr)), Hashable (f (SR.SemiRingBase sr))) =>
  SR.SemiRingRepr sr ->
  [(f (SR.SemiRingBase sr), Natural)] ->
  SRProd sr f
fromTerms sr terms =
  SRProd
    (BKv.fromList (P.+) (P.filter (\(_, e) -> e P./= 0) terms))
    (SR.one sr)
    sr

-- | Convert a product to a list of terms and their exponents
toTerms :: SRProd sr f -> [(f (SR.SemiRingBase sr), Natural)]
toTerms = BKv.toList . prodMap

-- | Multiply two products
mul ::
  (Eq (f (SR.SemiRingBase sr)), Ord (f (SR.SemiRingBase sr)), Hashable (f (SR.SemiRingBase sr))) =>
  SRProd sr f ->
  SRProd sr f ->
  SRProd sr f
mul p1 p2 =
  let sr = prodRepr p1
  in SRProd
       (BKv.merge (P.+) (prodMap p1) (prodMap p2))
       (SR.mul sr (prodCoeff p1) (prodCoeff p2))
       sr

-- | Multiply by a variable
mulVar ::
  (Eq (f (SR.SemiRingBase sr)), Hashable (f (SR.SemiRingBase sr))) =>
  SRProd sr f ->
  f (SR.SemiRingBase sr) ->
  SRProd sr f
mulVar p x =
  SRProd
    (BKv.insert (P.+) (prodMap p) x 1)
    (prodCoeff p)
    (prodRepr p)

-- | Multiply by a constant (scale the coefficient)
scale :: SRProd sr f -> SR.Coefficient sr -> SRProd sr f
scale p c =
  let sr = prodRepr p
  in SRProd
       (prodMap p)
       (SR.mul sr (prodCoeff p) c)
       sr

-- | Check if the product is a constant (no variable terms)
asConstant :: SRProd sr f -> Maybe (SR.Coefficient sr)
asConstant p
  | BKv.isEmpty (prodMap p) = Just (prodCoeff p)
  | otherwise = Nothing

-- | Check if the product is a single variable with coefficient 1
asVar :: SRProd sr f -> Maybe (f (SR.SemiRingBase sr))
asVar p
  | [(x, e)] <- BKv.toList (prodMap p)
  , e P.== 1
  , SR.eq (prodRepr p) (prodCoeff p) (SR.one (prodRepr p))
  = Just x
  | otherwise = Nothing

-- | Check if a variable appears in the product
contains ::
  (Eq (f (SR.SemiRingBase sr)), Hashable (f (SR.SemiRingBase sr))) =>
  SRProd sr f ->
  f (SR.SemiRingBase sr) ->
  Bool
contains p x = P.not (BKv.isEmpty (BKv.insert (P.+) BKv.empty x 0))

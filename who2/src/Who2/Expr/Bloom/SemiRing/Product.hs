{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Products over semirings using BloomKv for efficient small maps
module Who2.Expr.Bloom.SemiRing.Product
  ( SRProd(..)
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
  , size
  , threshold
  ) where

import Data.Bits (xor, (.&.))
import Data.Hashable (Hashable(hash, hashWithSalt))
import Data.Kind (Type)
import Numeric.Natural (Natural)

import qualified Data.BitVector.Sized as BV
import qualified What4.BaseTypes as BT
import qualified What4.SemiRing as SR
import qualified What4.Utils.AbstractDomains as AD
import qualified What4.Utils.BVDomain as BVD

import qualified Who2.Expr.Bloom.Map as BKv

------------------------------------------------------------------------
-- Type and instances
------------------------------------------------------------------------

-- | A product of semiring values using BloomKv.
--
-- Represents: coeff * product_i (term_i ^ exponent_i)
--
-- INVARIANT: Exponents should not be zero and terms should not be
-- constants (i.e., their abstract value is a singleton). This is not a safety
-- invariant, but helps ensure normalized terms.
data SRProd (sr :: SR.SemiRing) (f :: BT.BaseType -> Type) = SRProd
  { prodMap :: !(BKv.BloomKv (f (SR.SemiRingBase sr)) Natural)
    -- ^ Map from terms to their exponents
  , prodCoeff :: !(SR.Coefficient sr)
    -- ^ Constant coefficient
  , prodRepr :: !(SR.SemiRingRepr sr)
    -- ^ Runtime representation of the semiring
  }

-- Note: Manual Show instance to avoid needing Show for SemiRingRepr
instance (Show (f (SR.SemiRingBase sr)), Show (SR.Coefficient sr)) => Show (SRProd sr f) where
  show p = "SRProd { prodMap = " ++ show (prodMap p) ++
           ", prodCoeff = " ++ show (prodCoeff p) ++ " }"

eqBy2 ::
  (SR.Coefficient sr -> SR.Coefficient sr -> Bool) ->
  (f (SR.SemiRingBase sr) -> f (SR.SemiRingBase sr) -> Bool) ->
  SRProd sr f ->
  SRProd sr f ->
  Bool
eqBy2 eqCoeff eqTerm p1 p2 =
  eqCoeff (prodCoeff p1) (prodCoeff p2)
  && BKv.eqBy2 eqTerm (==) (prodMap p1) (prodMap p2)
{-# INLINE eqBy2 #-}

-- | Like 'liftEq', but without typeclass constraints (uses standard Eq for coefficient comparison)
eqBy ::
  (f (SR.SemiRingBase sr) -> f (SR.SemiRingBase sr) -> Bool) ->
  SRProd sr f ->
  SRProd sr f ->
  Bool
eqBy eqTerm p1 p2 = eqBy2 (SR.eq (prodRepr p1)) eqTerm p1 p2
{-# INLINE eqBy #-}

-- test-law: propSRProductCustomEqReflexivity
-- test-law: propSRProductCustomEqSymmetry
-- test-law: propSRProductCustomEqTransitivity
-- | @'eqBy' (==)@
instance
  ( Eq (f (SR.SemiRingBase sr))
  , Eq (SR.Coefficient sr)
  ) => Eq (SRProd sr f) where
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
    EQ -> BKv.ordBy2 cmpTerm compare (prodMap p1) (prodMap p2)
    other -> other
{-# INLINE ordBy2 #-}

-- | Like 'liftCompare', but without typeclass constraints (uses standard Ord for coefficient comparison)
ordBy ::
  (f (SR.SemiRingBase sr) -> f (SR.SemiRingBase sr) -> Ordering) ->
  SRProd sr f ->
  SRProd sr f ->
  Ordering
ordBy cmpTerm p1 p2 = ordBy2 (SR.sr_compare (prodRepr p1)) cmpTerm p1 p2
{-# INLINE ordBy #-}

-- test-law: propSRProductCustomOrdReflexivity
-- test-law: propSRProductCustomOrdAntisymmetry
-- test-law: propSRProductCustomOrdTransitivity
-- test-law: propSRProductCustomOrdEqConsistency
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
  hash p = hash (prodCoeff p) `hashWithSalt` hash (prodMap p)
  hashWithSalt salt p = salt `xor` hash p

------------------------------------------------------------------------
-- Operations
------------------------------------------------------------------------

-- | Returns 'Just' when the abstract value is a singleton.
asCoeff ::
  AD.HasAbsValue f =>
  SR.SemiRingRepr sr ->
  f (SR.SemiRingBase sr) ->
  Maybe (SR.Coefficient sr)
asCoeff =
  \case
    SR.SemiRingIntegerRepr -> AD.asSingleRange . AD.getAbsValue
    SR.SemiRingRealRepr -> AD.asSingleRange . AD.ravRange . AD.getAbsValue
    SR.SemiRingBVRepr _ w -> fmap (BV.mkBV w) . BVD.asSingleton . AD.getAbsValue
{-# INLINE asCoeff #-}

-- | Raise a coefficient to a Natural power using exponentiation by squaring
pow :: SR.SemiRingRepr sr -> SR.Coefficient sr -> Natural -> SR.Coefficient sr
pow sr c n
  | n == 0 = SR.one sr
  | n == 1 = c
  | n .&. 1 == 0 = let h = pow sr c (n `div` 2) in SR.mul sr h h  -- even
  | otherwise = SR.mul sr c (pow sr c (n - 1))  -- odd
{-# INLINE pow #-}

-- | Create a constant product
constant :: SR.SemiRingRepr sr -> SR.Coefficient sr -> SRProd sr f
constant sr c = SRProd BKv.empty c sr

-- | Create the multiplicative identity (empty product with coefficient 1)
one :: SR.SemiRingRepr sr -> SRProd sr f
one sr = SRProd BKv.empty (SR.one sr) sr

-- | Create a product from a single variable (coefficient 1)
var ::
  ( AD.HasAbsValue f
  , Eq (f (SR.SemiRingBase sr))
  , Hashable (f (SR.SemiRingBase sr))
  , Hashable Natural
  ) =>
  SR.SemiRingRepr sr ->
  f (SR.SemiRingBase sr) ->
  SRProd sr f
var sr x
  | Just c <- asCoeff sr x = constant sr c  -- x^1 = c
  | otherwise = SRProd (BKv.singleton x 1) (SR.one sr) sr

-- | Create a product from a list of terms and their exponents (coefficient 1)
fromTerms ::
  ( AD.HasAbsValue f
  , Eq (f (SR.SemiRingBase sr))
  , Hashable (f (SR.SemiRingBase sr))
  , Hashable Natural
  ) =>
  SR.SemiRingRepr sr ->
  [(f (SR.SemiRingBase sr), Natural)] ->
  SRProd sr f
fromTerms sr terms =
  let (nonConstTerms, constCoeff) = foldr go ([], SR.one sr) terms
      go (x, e) (ts, coeff) =
        if e == 0
        then (ts, coeff)
        else case asCoeff sr x of
          Just c -> (ts, SR.mul sr coeff (pow sr c e))  -- fold c^e into coefficient
          Nothing -> ((x, e) : ts, coeff)
  in SRProd
      (BKv.fromList addExp nonConstTerms)
      constCoeff
      sr
  where
    addExp e1 e2 = let e' = e1 + e2 in if e' == 0 then Nothing else Just e'

-- | Convert a product to a list of terms and their exponents
toTerms :: SRProd sr f -> [(f (SR.SemiRingBase sr), Natural)]
toTerms = BKv.toList . prodMap

-- | Multiply two products
mul ::
  (Eq (f (SR.SemiRingBase sr)), Ord (f (SR.SemiRingBase sr)), Hashable (f (SR.SemiRingBase sr)), Hashable Natural) =>
  SRProd sr f ->
  SRProd sr f ->
  SRProd sr f
mul p1 p2 =
  let sr = prodRepr p1
  in SRProd
       (BKv.merge addExp (prodMap p1) (prodMap p2))
       (SR.mul sr (prodCoeff p1) (prodCoeff p2))
       sr
  where
    addExp e1 e2 = let e' = e1 + e2 in if e' == 0 then Nothing else Just e'

-- | Multiply by a variable
mulVar ::
  ( AD.HasAbsValue f
  , Eq (f (SR.SemiRingBase sr))
  , Hashable (f (SR.SemiRingBase sr))
  , Hashable Natural
  ) =>
  SRProd sr f ->
  f (SR.SemiRingBase sr) ->
  SRProd sr f
mulVar p x
  | Just c <- asCoeff sr x = scale p c  -- multiply coeff by c^1
  | otherwise =
      SRProd
        (BKv.insert addExp (prodMap p) x 1)
        (prodCoeff p)
        sr
  where
    sr = prodRepr p
    addExp e1 e2 = let e' = e1 + e2 in if e' == 0 then Nothing else Just e'

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
  , e == 1
  , SR.eq (prodRepr p) (prodCoeff p) (SR.one (prodRepr p))
  = Just x
  | otherwise = Nothing

-- | Check if a variable appears in the product
contains ::
  (Eq (f (SR.SemiRingBase sr)), Hashable (f (SR.SemiRingBase sr))) =>
  SRProd sr f ->
  f (SR.SemiRingBase sr) ->
  Bool
contains p x = not (BKv.isEmpty (BKv.insert addExp (prodMap p) x 1))
  where
    addExp e1 e2 = let e' = e1 + e2 in if e' == 0 then Nothing else Just e'

-- | Get the number of terms in the product
size :: SRProd sr f -> Int
size = BKv.size . prodMap
{-# INLINE size #-}

-- | The threshold for the underlying BloomKv
threshold :: Int
threshold = BKv.threshold
{-# INLINE threshold #-}

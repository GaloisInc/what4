{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
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

import qualified Control.Exception as Ex
import Data.Hashable (Hashable(hashWithSalt))
import Data.Kind (Type)
import qualified Data.Maybe as Maybe
import qualified Data.BitVector.Sized as BV

import qualified What4.SemiRing as SR
import qualified What4.BaseTypes as BT
import qualified What4.Utils.AbstractDomains as AD
import qualified What4.Utils.BVDomain as BVD

import qualified Who2.Expr.HashConsed.Map as EM
import Who2.Expr (HasId)

------------------------------------------------------------------------
-- Type and instances
------------------------------------------------------------------------

-- | A hash-consed sum of semiring values using ExprMap.
--
-- INVARIANT: Coefficients should not be zero and terms should not be
-- constants (i.e., according to 'exprIsConst'). This is not a safety
-- invariant, but helps ensure normalized terms.
data SRSum (sr :: SR.SemiRing) (f :: BT.BaseType -> Type) = SRSum
  { sumMap :: !(EM.ExprMap (f (SR.SemiRingBase sr)) (SR.Coefficient sr))
    -- ^ Map from terms to their coefficients
  , sumOffsetHC :: !(SR.Coefficient sr)
    -- ^ Constant offset
  , sumReprHC :: !(SR.SemiRingRepr sr)
    -- ^ Runtime representation of the semiring
  }

-- Note: Manual Show instance to avoid needing Show for SemiRingRepr
instance (Show (f (SR.SemiRingBase sr)), Show (SR.Coefficient sr)) => Show (SRSum sr f) where
  show ws = "SRSum { sumMap = " ++ show (sumMap ws) ++
            ", sumOffset = " ++ show (sumOffsetHC ws) ++ " }"

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

-- test-law: propSRSumCustomEqReflexivity
-- test-law: propSRSumCustomEqSymmetry
-- test-law: propSRSumCustomEqTransitivity
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

-- test-law: propSRSumCustomOrdReflexivity
-- test-law: propSRSumCustomOrdAntisymmetry
-- test-law: propSRSumCustomOrdTransitivity
-- test-law: propSRSumCustomOrdEqConsistency
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

-- | Check if an expression is a constant based on abstract value
exprIsConst ::
  AD.HasAbsValue f =>
  SR.SemiRingRepr sr ->
  f (SR.SemiRingBase sr) ->
  Bool
exprIsConst sr x = Maybe.isJust (asCoeff sr x)
{-# INLINE exprIsConst #-}

sumOffset :: SRSum sr f -> SR.Coefficient sr
sumOffset = sumOffsetHC
{-# INLINE sumOffset #-}

sumRepr :: SRSum sr f -> SR.SemiRingRepr sr
sumRepr = sumReprHC
{-# INLINE sumRepr #-}

constant :: SR.SemiRingRepr sr -> SR.Coefficient sr -> SRSum sr f
constant sr c = SRSum EM.empty c sr
{-# INLINE constant #-}

var ::
  ( AD.HasAbsValue f
  , HasId (f (SR.SemiRingBase sr))
  ) =>
  SR.SemiRingRepr sr ->
  f (SR.SemiRingBase sr) ->
  SRSum sr f
var sr x = affineVar sr (SR.one sr) x (SR.zero sr)
{-# INLINE var #-}

affineVar ::
  ( AD.HasAbsValue f
  , HasId (f (SR.SemiRingBase sr))
  ) =>
  SR.SemiRingRepr sr ->
  SR.Coefficient sr ->
  f (SR.SemiRingBase sr) ->
  SR.Coefficient sr ->
  SRSum sr f
affineVar sr coeff x offset
  | SR.eq sr coeff (SR.zero sr) = constant sr offset
  | Just c <- asCoeff sr x = constant sr (SR.add sr (SR.mul sr coeff c) offset)
  | otherwise = SRSum (EM.singleton x coeff) offset sr

scaledVar ::
  ( AD.HasAbsValue f
  , HasId (f (SR.SemiRingBase sr))
  ) =>
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

add :: AD.HasAbsValue f => SRSum sr f -> SRSum sr f -> SRSum sr f
add ws1 ws2 =
  SRSum
    (EM.unionWithMaybe addCoeff (sumMap ws1) (sumMap ws2))
    (SR.add sr (sumOffsetHC ws1) (sumOffsetHC ws2))
    sr
  where
    sr = sumReprHC ws1
    addCoeff v1 v2 =
      let v' = SR.add sr v1 v2
      in if SR.eq sr v' (SR.zero sr) then Nothing else Just v'
{-# INLINE add #-}

addVar ::
  ( AD.HasAbsValue f
  , HasId (f (SR.SemiRingBase sr))
  ) =>
  SRSum sr f ->
  f (SR.SemiRingBase sr) ->
  SRSum sr f
addVar ws x =
  Ex.assert (not (exprIsConst sr x)) $
    SRSum
      (EM.insertWithMaybe addCoeff x (SR.one sr) (sumMap ws))
      (sumOffsetHC ws)
      sr
  where
    sr = sumReprHC ws
    addCoeff v1 v2 =
      let v' = SR.add sr v1 v2
      in if SR.eq sr v' (SR.zero sr) then Nothing else Just v'

addConstant :: SRSum sr f -> SR.Coefficient sr -> SRSum sr f
addConstant ws c =
  ws { sumOffsetHC = SR.add (sumReprHC ws) (sumOffsetHC ws) c }
{-# INLINE addConstant #-}

fromTerms ::
  ( AD.HasAbsValue f
  , HasId (f (SR.SemiRingBase sr))
  ) =>
  SR.SemiRingRepr sr ->
  [(f (SR.SemiRingBase sr), SR.Coefficient sr)] ->
  SR.Coefficient sr ->
  SRSum sr f
fromTerms sr terms offset =
  let (nonConstTerms, constOffset) = foldr go ([], SR.zero sr) terms
      go (x, c) (ts, acc) =
        if SR.eq sr c (SR.zero sr)
        then (ts, acc)
        else case asCoeff sr x of
          Just xc -> (ts, SR.add sr (SR.mul sr c xc) acc)
          Nothing -> ((x, c) : ts, acc)
  in SRSum
      (foldr (\(k, v) m -> EM.insertWithMaybe addCoeff k v m) EM.empty nonConstTerms)
      (SR.add sr offset constOffset)
      sr
  where
    addCoeff v1 v2 =
      let v' = SR.add sr v1 v2
      in if SR.eq sr v' (SR.zero sr) then Nothing else Just v'

toTerms :: SRSum sr f -> [(f (SR.SemiRingBase sr), SR.Coefficient sr)]
toTerms = EM.toList . sumMap
{-# INLINE toTerms #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Who2.Laws.Bloom.SemiRing.Sum
  ( -- eqBy properties
    propBloomSumEqByReflexive
  , propBloomSumEqBySymmetric
  , propBloomSumEqByTransitive
  -- ordBy properties
  , propBloomSumOrdByReflexive
  , propBloomSumOrdByAntisymmetric
  , propBloomSumOrdByTransitive
  , propBloomSumOrdByConsistentWithEqBy
  ) where

import Control.Monad (unless)

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Data.BitVector.Sized as BV

import Data.Parameterized.NatRepr (knownNat)

import qualified What4.SemiRing as SR

import qualified Who2.Expr.Bloom.SemiRing.Sum as SRS
import Who2.Laws.Helpers (MockExprBT(..), checkOrdTransitivity, checkOrdAntisymmetry)

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

genBloomSumBV8 :: H.Gen (SRS.SRSum (SR.SemiRingBV SR.BVArith 8) MockExprBT)
genBloomSumBV8 = do
  offset <- Gen.int (Range.linear 0 255)
  numTerms <- Gen.int (Range.linear 0 3)
  terms <- Gen.list (Range.singleton numTerms) $ do
    key <- MockExprBT <$> Gen.int (Range.linear 0 100)
    coeff <- Gen.int (Range.linear 0 255)
    pure (key, BV.mkBV knownNat (fromIntegral coeff))
  pure $ SRS.fromTerms (SR.SemiRingBVRepr SR.BVArithRepr knownNat) terms (BV.mkBV knownNat (fromIntegral offset))

-------------------------------------------------------------------------------
-- eqBy Properties
-------------------------------------------------------------------------------

propBloomSumEqByReflexive :: Property
propBloomSumEqByReflexive = H.property $ do
  s <- H.forAll genBloomSumBV8
  H.assert $ SRS.eqBy (==) s s

propBloomSumEqBySymmetric :: Property
propBloomSumEqBySymmetric = H.property $ do
  s1 <- H.forAll genBloomSumBV8
  s2 <- H.forAll genBloomSumBV8
  let eq1 = SRS.eqBy (==) s1 s2
  let eq2 = SRS.eqBy (==) s2 s1
  eq1 H.=== eq2

propBloomSumEqByTransitive :: Property
propBloomSumEqByTransitive = H.property $ do
  s1 <- H.forAll genBloomSumBV8
  s2 <- H.forAll genBloomSumBV8
  s3 <- H.forAll genBloomSumBV8
  let eq12 = SRS.eqBy (==) s1 s2
  let eq23 = SRS.eqBy (==) s2 s3
  let eq13 = SRS.eqBy (==) s1 s3
  unless (not eq12 || not eq23 || eq13) H.failure

-------------------------------------------------------------------------------
-- ordBy Properties
-------------------------------------------------------------------------------

propBloomSumOrdByReflexive :: Property
propBloomSumOrdByReflexive = H.property $ do
  s <- H.forAll genBloomSumBV8
  SRS.ordBy compare s s H.=== EQ

propBloomSumOrdByAntisymmetric :: Property
propBloomSumOrdByAntisymmetric = H.property $ do
  s1 <- H.forAll genBloomSumBV8
  s2 <- H.forAll genBloomSumBV8
  let ord1 = SRS.ordBy compare s1 s2
  let ord2 = SRS.ordBy compare s2 s1
  unless (checkOrdAntisymmetry ord1 ord2) H.failure

propBloomSumOrdByTransitive :: Property
propBloomSumOrdByTransitive = H.property $ do
  s1 <- H.forAll genBloomSumBV8
  s2 <- H.forAll genBloomSumBV8
  s3 <- H.forAll genBloomSumBV8
  let ord12 = SRS.ordBy compare s1 s2
  let ord23 = SRS.ordBy compare s2 s3
  let ord13 = SRS.ordBy compare s1 s3
  unless (checkOrdTransitivity ord12 ord23 ord13) H.failure

propBloomSumOrdByConsistentWithEqBy :: Property
propBloomSumOrdByConsistentWithEqBy = H.property $ do
  s1 <- H.forAll genBloomSumBV8
  s2 <- H.forAll genBloomSumBV8
  let eq = SRS.eqBy (==) s1 s2
  let ord = SRS.ordBy compare s1 s2
  let result = case (eq, ord) of
        (True, EQ) -> True
        (False, LT) -> True
        (False, GT) -> True
        (True, LT) -> False
        (True, GT) -> False
        (False, EQ) -> False
  unless result H.failure

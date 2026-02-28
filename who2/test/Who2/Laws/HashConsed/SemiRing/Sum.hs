{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Who2.Laws.HashConsed.SemiRing.Sum (tests) where

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Data.BitVector.Sized as BV
import Data.Parameterized.NatRepr (knownNat)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import qualified What4.SemiRing as SR

import qualified Who2.Expr.HashConsed.SemiRing.Sum as HCSR
import Who2.Laws.Helpers (MockExprBT(..), checkEqReflexivity, checkEqSymmetry, checkEqTransitivity, checkOrdTransitivity, checkOrdAntisymmetry, checkOrdEqConsistency)

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

genHashConsedSumBV8 :: H.Gen (HCSR.SRSum (SR.SemiRingBV SR.BVArith 8) MockExprBT)
genHashConsedSumBV8 = do
  offset <- Gen.int (Range.linear 0 255)
  numTerms <- Gen.int (Range.linear 0 3)
  terms <- Gen.list (Range.singleton numTerms) $ do
    key <- MockExprBT <$> Gen.int (Range.linear 0 100)
    coeff <- Gen.int (Range.linear 0 255)
    pure (key, BV.mkBV knownNat (fromIntegral coeff))
  pure $ HCSR.fromTerms (SR.SemiRingBVRepr SR.BVArithRepr knownNat) terms (BV.mkBV knownNat (fromIntegral offset))

-------------------------------------------------------------------------------
-- Custom Equality (eqBy)
-- Note: SRSum uses semiring-specific equality, not Eq/Eq1 typeclass instances
-------------------------------------------------------------------------------

propSRSumCustomEqReflexivity :: Property
propSRSumCustomEqReflexivity = H.property $ do
  s <- H.forAll genHashConsedSumBV8
  H.assert $ checkEqReflexivity (HCSR.eqBy (==)) s

propSRSumCustomEqSymmetry :: Property
propSRSumCustomEqSymmetry = H.property $ do
  s1 <- H.forAll genHashConsedSumBV8
  s2 <- H.forAll genHashConsedSumBV8
  H.assert $ checkEqSymmetry (HCSR.eqBy (==)) (HCSR.eqBy (==)) s1 s2

propSRSumCustomEqTransitivity :: Property
propSRSumCustomEqTransitivity = H.property $ do
  s1 <- H.forAll genHashConsedSumBV8
  s2 <- H.forAll genHashConsedSumBV8
  s3 <- H.forAll genHashConsedSumBV8
  let eq12 = HCSR.eqBy (==) s1 s2
  let eq23 = HCSR.eqBy (==) s2 s3
  let eq13 = HCSR.eqBy (==) s1 s3
  H.assert $ checkEqTransitivity eq12 eq23 eq13

-------------------------------------------------------------------------------
-- Custom Ordering (ordBy)
-- Note: SRSum uses semiring-specific ordering, not Ord/Ord1 typeclass instances
-------------------------------------------------------------------------------

propSRSumCustomOrdReflexivity :: Property
propSRSumCustomOrdReflexivity = H.property $ do
  s <- H.forAll genHashConsedSumBV8
  HCSR.ordBy compare s s H.=== EQ

propSRSumCustomOrdAntisymmetry :: Property
propSRSumCustomOrdAntisymmetry = H.property $ do
  s1 <- H.forAll genHashConsedSumBV8
  s2 <- H.forAll genHashConsedSumBV8
  let ord1 = HCSR.ordBy compare s1 s2
  let ord2 = HCSR.ordBy compare s2 s1
  H.assert $ checkOrdAntisymmetry ord1 ord2

propSRSumCustomOrdTransitivity :: Property
propSRSumCustomOrdTransitivity = H.property $ do
  s1 <- H.forAll genHashConsedSumBV8
  s2 <- H.forAll genHashConsedSumBV8
  s3 <- H.forAll genHashConsedSumBV8
  let ord12 = HCSR.ordBy compare s1 s2
  let ord23 = HCSR.ordBy compare s2 s3
  let ord13 = HCSR.ordBy compare s1 s3
  H.assert $ checkOrdTransitivity ord12 ord23 ord13

propSRSumCustomOrdEqConsistency :: Property
propSRSumCustomOrdEqConsistency = H.property $ do
  s1 <- H.forAll genHashConsedSumBV8
  s2 <- H.forAll genHashConsedSumBV8
  let eq = HCSR.eqBy (==) s1 s2
  let ord = HCSR.ordBy compare s1 s2
  H.assert $ checkOrdEqConsistency eq ord

-------------------------------------------------------------------------------
-- Test Tree
-------------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "HashConsed.Sum"
  [ testGroup "Custom Equality (eqBy)"
      [ testProperty "Reflexivity (eqBy (==) x x)" $
          H.withTests 1000 propSRSumCustomEqReflexivity
      , testProperty "Symmetry" $
          H.withTests 1000 propSRSumCustomEqSymmetry
      , testProperty "Transitivity" $
          H.withTests 1000 propSRSumCustomEqTransitivity
      ]
  , testGroup "Custom Ordering (ordBy)"
      [ testProperty "Reflexivity (ordBy compare x x == EQ)" $
          H.withTests 1000 propSRSumCustomOrdReflexivity
      , testProperty "Antisymmetry" $
          H.withTests 1000 propSRSumCustomOrdAntisymmetry
      , testProperty "Transitivity" $
          H.withTests 1000 propSRSumCustomOrdTransitivity
      , testProperty "Consistency with eqBy" $
          H.withTests 1000 propSRSumCustomOrdEqConsistency
      ]
  ]

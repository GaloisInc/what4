{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Who2.Laws.Bloom.SemiRing.Product (tests) where

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Data.BitVector.Sized()
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import Data.Parameterized.NatRepr (knownNat)

import qualified What4.SemiRing as SR

import qualified Who2.Expr.Bloom.SemiRing.Product as SRP
import Who2.Laws.Helpers (MockExprBT(..), checkEqReflexivity, checkEqSymmetry, checkEqTransitivity, checkOrdTransitivity, checkOrdAntisymmetry, checkOrdEqConsistency)

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

genBloomProductBV8 :: H.Gen (SRP.SRProd (SR.SemiRingBV SR.BVBits 8) MockExprBT)
genBloomProductBV8 = do
  numTerms <- Gen.int (Range.linear 0 3)
  terms <- Gen.list (Range.singleton numTerms) $ do
    key <- MockExprBT <$> Gen.int (Range.linear 0 100)
    expnt <- Gen.integral (Range.linear 1 5)
    pure (key, expnt)
  pure $ SRP.fromTerms (SR.SemiRingBVRepr SR.BVBitsRepr knownNat) terms

-------------------------------------------------------------------------------
-- Custom Equality (eqBy)
-- Note: SRProd uses semiring-specific equality, not Eq/Eq1 typeclass instances
-------------------------------------------------------------------------------

propSRProductCustomEqReflexivity :: Property
propSRProductCustomEqReflexivity = H.property $ do
  p <- H.forAll genBloomProductBV8
  H.assert $ checkEqReflexivity (SRP.eqBy (==)) p

propSRProductCustomEqSymmetry :: Property
propSRProductCustomEqSymmetry = H.property $ do
  p1 <- H.forAll genBloomProductBV8
  p2 <- H.forAll genBloomProductBV8
  H.assert $ checkEqSymmetry (SRP.eqBy (==)) (SRP.eqBy (==)) p1 p2

propSRProductCustomEqTransitivity :: Property
propSRProductCustomEqTransitivity = H.property $ do
  p1 <- H.forAll genBloomProductBV8
  p2 <- H.forAll genBloomProductBV8
  p3 <- H.forAll genBloomProductBV8
  let eq12 = SRP.eqBy (==) p1 p2
  let eq23 = SRP.eqBy (==) p2 p3
  let eq13 = SRP.eqBy (==) p1 p3
  H.assert $ checkEqTransitivity eq12 eq23 eq13

-------------------------------------------------------------------------------
-- Custom Ordering (ordBy)
-- Note: SRProd uses semiring-specific ordering, not Ord/Ord1 typeclass instances
-------------------------------------------------------------------------------

propSRProductCustomOrdReflexivity :: Property
propSRProductCustomOrdReflexivity = H.property $ do
  p <- H.forAll genBloomProductBV8
  SRP.ordBy compare p p H.=== EQ

propSRProductCustomOrdAntisymmetry :: Property
propSRProductCustomOrdAntisymmetry = H.property $ do
  p1 <- H.forAll genBloomProductBV8
  p2 <- H.forAll genBloomProductBV8
  let ord1 = SRP.ordBy compare p1 p2
  let ord2 = SRP.ordBy compare p2 p1
  H.assert $ checkOrdAntisymmetry ord1 ord2

propSRProductCustomOrdTransitivity :: Property
propSRProductCustomOrdTransitivity = H.property $ do
  p1 <- H.forAll genBloomProductBV8
  p2 <- H.forAll genBloomProductBV8
  p3 <- H.forAll genBloomProductBV8
  let ord12 = SRP.ordBy compare p1 p2
  let ord23 = SRP.ordBy compare p2 p3
  let ord13 = SRP.ordBy compare p1 p3
  H.assert $ checkOrdTransitivity ord12 ord23 ord13

propSRProductCustomOrdEqConsistency :: Property
propSRProductCustomOrdEqConsistency = H.property $ do
  p1 <- H.forAll genBloomProductBV8
  p2 <- H.forAll genBloomProductBV8
  let eq = SRP.eqBy (==) p1 p2
  let ord = SRP.ordBy compare p1 p2
  H.assert $ checkOrdEqConsistency eq ord

-------------------------------------------------------------------------------
-- Test Tree
-------------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "Bloom.Product"
  [ testGroup "Custom Equality (eqBy)"
      [ testProperty "Reflexivity (eqBy (==) x x)" $
          H.withTests 1000 propSRProductCustomEqReflexivity
      , testProperty "Symmetry" $
          H.withTests 1000 propSRProductCustomEqSymmetry
      , testProperty "Transitivity" $
          H.withTests 1000 propSRProductCustomEqTransitivity
      ]
  , testGroup "Custom Ordering (ordBy)"
      [ testProperty "Reflexivity (ordBy compare x x == EQ)" $
          H.withTests 1000 propSRProductCustomOrdReflexivity
      , testProperty "Antisymmetry" $
          H.withTests 1000 propSRProductCustomOrdAntisymmetry
      , testProperty "Transitivity" $
          H.withTests 1000 propSRProductCustomOrdTransitivity
      , testProperty "Consistency with eqBy" $
          H.withTests 1000 propSRProductCustomOrdEqConsistency
      ]
  ]

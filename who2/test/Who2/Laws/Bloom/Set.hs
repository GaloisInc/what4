module Who2.Laws.Bloom.Set (tests) where

import Data.Functor.Classes (Eq1(liftEq), Ord1(liftCompare))
import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import qualified Who2.Expr.Bloom.Set as BS
import Who2.Laws.Helpers (checkEqReflexivity, checkEqSymmetry, checkEqTransitivity, checkOrdTransitivity, checkOrdAntisymmetry, checkOrdEqConsistency)

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

genBloomSeqInt :: H.Gen (BS.BloomSeq Int)
genBloomSeqInt = do
  list <- Gen.list (Range.linear 0 10) (Gen.int (Range.linear 0 100))
  pure $ BS.fromList list

-------------------------------------------------------------------------------
-- Eq Laws
-------------------------------------------------------------------------------

propBloomSeqEqReflexivity :: Property
propBloomSeqEqReflexivity = H.property $ do
  bs <- H.forAll genBloomSeqInt
  H.assert $ checkEqReflexivity (==) bs

propBloomSeqEqSymmetry :: Property
propBloomSeqEqSymmetry = H.property $ do
  bs1 <- H.forAll genBloomSeqInt
  bs2 <- H.forAll genBloomSeqInt
  H.assert $ checkEqSymmetry (==) (==) bs1 bs2

propBloomSeqEqTransitivity :: Property
propBloomSeqEqTransitivity = H.property $ do
  bs1 <- H.forAll genBloomSeqInt
  bs2 <- H.forAll genBloomSeqInt
  bs3 <- H.forAll genBloomSeqInt
  let eq12 = bs1 == bs2
  let eq23 = bs2 == bs3
  let eq13 = bs1 == bs3
  H.assert $ checkEqTransitivity eq12 eq23 eq13

-------------------------------------------------------------------------------
-- Eq1 Consistency
-------------------------------------------------------------------------------

propBloomSeqEq1Consistency :: Property
propBloomSeqEq1Consistency = H.property $ do
  bs1 <- H.forAll genBloomSeqInt
  bs2 <- H.forAll genBloomSeqInt
  liftEq (==) bs1 bs2 H.=== (bs1 == bs2)

-------------------------------------------------------------------------------
-- Ord Laws
-------------------------------------------------------------------------------

propBloomSeqOrdReflexivity :: Property
propBloomSeqOrdReflexivity = H.property $ do
  bs <- H.forAll genBloomSeqInt
  compare bs bs H.=== EQ

propBloomSeqOrdAntisymmetry :: Property
propBloomSeqOrdAntisymmetry = H.property $ do
  bs1 <- H.forAll genBloomSeqInt
  bs2 <- H.forAll genBloomSeqInt
  let ord1 = compare bs1 bs2
  let ord2 = compare bs2 bs1
  H.assert $ checkOrdAntisymmetry ord1 ord2

propBloomSeqOrdTransitivity :: Property
propBloomSeqOrdTransitivity = H.property $ do
  bs1 <- H.forAll genBloomSeqInt
  bs2 <- H.forAll genBloomSeqInt
  bs3 <- H.forAll genBloomSeqInt
  let ord12 = compare bs1 bs2
  let ord23 = compare bs2 bs3
  let ord13 = compare bs1 bs3
  H.assert $ checkOrdTransitivity ord12 ord23 ord13

propBloomSeqOrdEqConsistency :: Property
propBloomSeqOrdEqConsistency = H.property $ do
  bs1 <- H.forAll genBloomSeqInt
  bs2 <- H.forAll genBloomSeqInt
  let eq = bs1 == bs2
  let ord = compare bs1 bs2
  H.assert $ checkOrdEqConsistency eq ord

-------------------------------------------------------------------------------
-- Ord1 Consistency
-------------------------------------------------------------------------------

propBloomSeqOrd1Consistency :: Property
propBloomSeqOrd1Consistency = H.property $ do
  bs1 <- H.forAll genBloomSeqInt
  bs2 <- H.forAll genBloomSeqInt
  liftCompare compare bs1 bs2 H.=== compare bs1 bs2

-------------------------------------------------------------------------------
-- Test Tree
-------------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "Bloom.Seq"
  [ testGroup "Eq Laws"
      [ testProperty "Reflexivity (x == x)" $
          H.withTests 1000 propBloomSeqEqReflexivity
      , testProperty "Symmetry (x == y <==> y == x)" $
          H.withTests 1000 propBloomSeqEqSymmetry
      , testProperty "Transitivity" $
          H.withTests 1000 propBloomSeqEqTransitivity
      ]
  , testGroup "Eq1 Consistency"
      [ testProperty "liftEq (==) behaves like (==)" $
          H.withTests 1000 propBloomSeqEq1Consistency
      ]
  , testGroup "Ord Laws"
      [ testProperty "Reflexivity (compare x x == EQ)" $
          H.withTests 1000 propBloomSeqOrdReflexivity
      , testProperty "Antisymmetry" $
          H.withTests 1000 propBloomSeqOrdAntisymmetry
      , testProperty "Transitivity" $
          H.withTests 1000 propBloomSeqOrdTransitivity
      , testProperty "Consistency with Eq" $
          H.withTests 1000 propBloomSeqOrdEqConsistency
      ]
  , testGroup "Ord1 Consistency"
      [ testProperty "liftCompare compare behaves like compare" $
          H.withTests 1000 propBloomSeqOrd1Consistency
      ]
  ]

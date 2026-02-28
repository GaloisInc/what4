module Who2.Laws.Bloom.Polarized (tests) where

import Data.Functor.Classes (Eq1(liftEq), Ord1(liftCompare))

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import qualified Who2.Expr.Bloom.Polarized as PBS
import Who2.Laws.Helpers (checkEqReflexivity, checkEqSymmetry, checkEqTransitivity, checkOrdTransitivity, checkOrdAntisymmetry, checkOrdEqConsistency)

-------------------------------------------------------------------------------
-- Generator and Instance
-------------------------------------------------------------------------------

genPolarizedBloomSeqInt :: H.Gen (PBS.PolarizedBloomSeq Int)
genPolarizedBloomSeqInt = do
  x <- Gen.int (Range.linear 1 50)
  y <- Gen.int (Range.linear 51 100)  -- Ensure x /= y
  -- fromTwo with distinct positive ints always gives Merged
  case PBS.fromTwo x y of
    PBS.Merged pbs -> pure pbs
    _ -> error "Unexpected: fromTwo with distinct positive ints should give Merged"

instance PBS.Polarizable Int where
  polarity x
    | x < 0 = PBS.Negative (negate x)
    | otherwise = PBS.Positive x

-------------------------------------------------------------------------------
-- Eq Laws
-------------------------------------------------------------------------------

propPolarizedBloomSeqEqReflexivity :: Property
propPolarizedBloomSeqEqReflexivity = H.property $ do
  pbs <- H.forAll genPolarizedBloomSeqInt
  H.assert $ checkEqReflexivity (==) pbs

propPolarizedBloomSeqEqSymmetry :: Property
propPolarizedBloomSeqEqSymmetry = H.property $ do
  pbs1 <- H.forAll genPolarizedBloomSeqInt
  pbs2 <- H.forAll genPolarizedBloomSeqInt
  H.assert $ checkEqSymmetry (==) (==) pbs1 pbs2

propPolarizedBloomSeqEqTransitivity :: Property
propPolarizedBloomSeqEqTransitivity = H.property $ do
  pbs1 <- H.forAll genPolarizedBloomSeqInt
  pbs2 <- H.forAll genPolarizedBloomSeqInt
  pbs3 <- H.forAll genPolarizedBloomSeqInt
  let eq12 = pbs1 == pbs2
  let eq23 = pbs2 == pbs3
  let eq13 = pbs1 == pbs3
  H.assert $ checkEqTransitivity eq12 eq23 eq13

-------------------------------------------------------------------------------
-- Eq1 Consistency
-------------------------------------------------------------------------------

propPolarizedBloomSeqEq1Consistency :: Property
propPolarizedBloomSeqEq1Consistency = H.property $ do
  pbs1 <- H.forAll genPolarizedBloomSeqInt
  pbs2 <- H.forAll genPolarizedBloomSeqInt
  liftEq (==) pbs1 pbs2 H.=== (pbs1 == pbs2)

-------------------------------------------------------------------------------
-- Ord Laws
-------------------------------------------------------------------------------

propPolarizedBloomSeqOrdReflexivity :: Property
propPolarizedBloomSeqOrdReflexivity = H.property $ do
  pbs <- H.forAll genPolarizedBloomSeqInt
  compare pbs pbs H.=== EQ

propPolarizedBloomSeqOrdAntisymmetry :: Property
propPolarizedBloomSeqOrdAntisymmetry = H.property $ do
  pbs1 <- H.forAll genPolarizedBloomSeqInt
  pbs2 <- H.forAll genPolarizedBloomSeqInt
  let ord1 = compare pbs1 pbs2
  let ord2 = compare pbs2 pbs1
  H.assert $ checkOrdAntisymmetry ord1 ord2

propPolarizedBloomSeqOrdTransitivity :: Property
propPolarizedBloomSeqOrdTransitivity = H.property $ do
  pbs1 <- H.forAll genPolarizedBloomSeqInt
  pbs2 <- H.forAll genPolarizedBloomSeqInt
  pbs3 <- H.forAll genPolarizedBloomSeqInt
  let ord12 = compare pbs1 pbs2
  let ord23 = compare pbs2 pbs3
  let ord13 = compare pbs1 pbs3
  H.assert $ checkOrdTransitivity ord12 ord23 ord13

propPolarizedBloomSeqOrdEqConsistency :: Property
propPolarizedBloomSeqOrdEqConsistency = H.property $ do
  pbs1 <- H.forAll genPolarizedBloomSeqInt
  pbs2 <- H.forAll genPolarizedBloomSeqInt
  let eq = pbs1 == pbs2
  let ord = compare pbs1 pbs2
  H.assert $ checkOrdEqConsistency eq ord

-------------------------------------------------------------------------------
-- Ord1 Consistency
-------------------------------------------------------------------------------

propPolarizedBloomSeqOrd1Consistency :: Property
propPolarizedBloomSeqOrd1Consistency = H.property $ do
  pbs1 <- H.forAll genPolarizedBloomSeqInt
  pbs2 <- H.forAll genPolarizedBloomSeqInt
  liftCompare compare pbs1 pbs2 H.=== compare pbs1 pbs2

-------------------------------------------------------------------------------
-- Test Tree
-------------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "Bloom.Polarized"
  [ testGroup "Eq Laws"
      [ testProperty "Reflexivity (x == x)" $
          H.withTests 1000 propPolarizedBloomSeqEqReflexivity
      , testProperty "Symmetry (x == y <==> y == x)" $
          H.withTests 1000 propPolarizedBloomSeqEqSymmetry
      , testProperty "Transitivity" $
          H.withTests 1000 propPolarizedBloomSeqEqTransitivity
      ]
  , testGroup "Eq1 Consistency"
      [ testProperty "liftEq (==) behaves like (==)" $
          H.withTests 1000 propPolarizedBloomSeqEq1Consistency
      ]
  , testGroup "Ord Laws"
      [ testProperty "Reflexivity (compare x x == EQ)" $
          H.withTests 1000 propPolarizedBloomSeqOrdReflexivity
      , testProperty "Antisymmetry" $
          H.withTests 1000 propPolarizedBloomSeqOrdAntisymmetry
      , testProperty "Transitivity" $
          H.withTests 1000 propPolarizedBloomSeqOrdTransitivity
      , testProperty "Consistency with Eq" $
          H.withTests 1000 propPolarizedBloomSeqOrdEqConsistency
      ]
  , testGroup "Ord1 Consistency"
      [ testProperty "liftCompare compare behaves like compare" $
          H.withTests 1000 propPolarizedBloomSeqOrd1Consistency
      ]
  ]

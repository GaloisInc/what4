module Who2.Laws.Bloom.HashedSeq (tests) where

import Control.Monad (when)

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Data.Functor.Classes (Ord1(liftCompare))
import Data.Hashable (hash)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import qualified Who2.Expr.Bloom.HashedSeq as HS
import qualified Who2.Laws.Helpers as Helpers

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

genHashedSeqInt :: H.Gen (HS.HashedSeq Int)
genHashedSeqInt = do
  list <- Gen.list (Range.linear 0 10) (Gen.int (Range.linear 0 100))
  pure $ HS.fromList list

-------------------------------------------------------------------------------
-- Eq Laws
-------------------------------------------------------------------------------

propHashedSeqEqReflexivity :: Property
propHashedSeqEqReflexivity = H.property $ do
  hs <- H.forAll genHashedSeqInt
  H.assert $ Helpers.checkEqReflexivity (==) hs

propHashedSeqEqSymmetry :: Property
propHashedSeqEqSymmetry = H.property $ do
  hs1 <- H.forAll genHashedSeqInt
  hs2 <- H.forAll genHashedSeqInt
  H.assert $ Helpers.checkEqSymmetry (==) (==) hs1 hs2

propHashedSeqEqTransitivity :: Property
propHashedSeqEqTransitivity = H.property $ do
  hs1 <- H.forAll genHashedSeqInt
  hs2 <- H.forAll genHashedSeqInt
  hs3 <- H.forAll genHashedSeqInt
  let eq12 = hs1 == hs2
  let eq23 = hs2 == hs3
  let eq13 = hs1 == hs3
  H.assert $ Helpers.checkEqTransitivity eq12 eq23 eq13

-------------------------------------------------------------------------------
-- Hashable Laws
-------------------------------------------------------------------------------

-- | HashedSeq should maintain hash consistency: equal sequences have equal hashes
propHashedSeqHashConsistency :: Property
propHashedSeqHashConsistency = H.property $ do
  hs1 <- H.forAll genHashedSeqInt
  hs2 <- H.forAll genHashedSeqInt
  when (hs1 == hs2) $ do
    hash hs1 H.=== hash hs2

-- | HashedSeq Eq instance should be consistent with list equality
propHashedSeqEqConsistency :: Property
propHashedSeqEqConsistency = H.property $ do
  hs1 <- H.forAll genHashedSeqInt
  hs2 <- H.forAll genHashedSeqInt
  let eq1 = hs1 == hs2
  let eq2 = HS.toList hs1 == HS.toList hs2
  eq1 H.=== eq2

-- | HashedSeq append (|>) should maintain hash consistency
propHashedSeqAppendHashConsistency :: Property
propHashedSeqAppendHashConsistency = H.property $ do
  hs <- H.forAll genHashedSeqInt
  x <- H.forAll $ Gen.int (Range.linear 0 100)
  let hs' = hs HS.|> x
  let fromList = HS.fromList (HS.toList hs ++ [x])
  hs' H.=== fromList
  hash hs' H.=== hash fromList

-- | HashedSeq merge (><) should maintain hash consistency
propHashedSeqMergeHashConsistency :: Property
propHashedSeqMergeHashConsistency = H.property $ do
  hs1 <- H.forAll genHashedSeqInt
  hs2 <- H.forAll genHashedSeqInt
  let hs' = hs1 HS.>< hs2
  let fromList = HS.fromList (HS.toList hs1 ++ HS.toList hs2)
  hs' H.=== fromList
  hash hs' H.=== hash fromList

-------------------------------------------------------------------------------
-- Ord Laws
-------------------------------------------------------------------------------

propHashedSeqOrdReflexivity :: Property
propHashedSeqOrdReflexivity = H.property $ do
  hs <- H.forAll genHashedSeqInt
  compare hs hs H.=== EQ

propHashedSeqOrdAntisymmetry :: Property
propHashedSeqOrdAntisymmetry = H.property $ do
  hs1 <- H.forAll genHashedSeqInt
  hs2 <- H.forAll genHashedSeqInt
  let ord1 = compare hs1 hs2
  let ord2 = compare hs2 hs1
  H.assert $ Helpers.checkOrdAntisymmetry ord1 ord2

propHashedSeqOrdTransitivity :: Property
propHashedSeqOrdTransitivity = H.property $ do
  hs1 <- H.forAll genHashedSeqInt
  hs2 <- H.forAll genHashedSeqInt
  hs3 <- H.forAll genHashedSeqInt
  let ord12 = compare hs1 hs2
  let ord23 = compare hs2 hs3
  let ord13 = compare hs1 hs3
  H.assert $ Helpers.checkOrdTransitivity ord12 ord23 ord13

propHashedSeqOrdEqConsistency :: Property
propHashedSeqOrdEqConsistency = H.property $ do
  hs1 <- H.forAll genHashedSeqInt
  hs2 <- H.forAll genHashedSeqInt
  let eq = hs1 == hs2
  let ord = compare hs1 hs2
  H.assert $ Helpers.checkOrdEqConsistency eq ord

-------------------------------------------------------------------------------
-- Ord1 Consistency
-------------------------------------------------------------------------------

propHashedSeqOrd1Consistency :: Property
propHashedSeqOrd1Consistency = H.property $ do
  hs1 <- H.forAll genHashedSeqInt
  hs2 <- H.forAll genHashedSeqInt
  liftCompare compare hs1 hs2 H.=== compare hs1 hs2

-------------------------------------------------------------------------------
-- Test Tree
-------------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "Bloom.HashedSeq"
  [ testGroup "Eq Laws"
      [ testProperty "Reflexivity (x == x)" $
          H.withTests 1000 propHashedSeqEqReflexivity
      , testProperty "Symmetry (x == y <==> y == x)" $
          H.withTests 1000 propHashedSeqEqSymmetry
      , testProperty "Transitivity" $
          H.withTests 1000 propHashedSeqEqTransitivity
      ]
  , testGroup "Hashable Laws"
      [ testProperty "Consistency with Eq (equal implies same hash)" $
          H.withTests 1000 propHashedSeqHashConsistency
      , testProperty "Eq consistency with list" $
          H.withTests 1000 propHashedSeqEqConsistency
      , testProperty "Append maintains hash consistency" $
          H.withTests 1000 propHashedSeqAppendHashConsistency
      , testProperty "Merge maintains hash consistency" $
          H.withTests 1000 propHashedSeqMergeHashConsistency
      ]
  , testGroup "Ord Laws"
      [ testProperty "Reflexivity (compare x x == EQ)" $
          H.withTests 1000 propHashedSeqOrdReflexivity
      , testProperty "Antisymmetry" $
          H.withTests 1000 propHashedSeqOrdAntisymmetry
      , testProperty "Transitivity" $
          H.withTests 1000 propHashedSeqOrdTransitivity
      , testProperty "Consistency with Eq" $
          H.withTests 1000 propHashedSeqOrdEqConsistency
      ]
  , testGroup "Ord1 Consistency"
      [ testProperty "liftCompare compare behaves like compare" $
          H.withTests 1000 propHashedSeqOrd1Consistency
      ]
  ]

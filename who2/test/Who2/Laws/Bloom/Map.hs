module Who2.Laws.Bloom.Map (tests) where

import Data.Functor.Classes (Eq1(liftEq), Ord1(liftCompare))

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import qualified Who2.Expr.Bloom.Map as BKv
import qualified Who2.Laws.Helpers as Helpers

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

genBloomKvIntString :: H.Gen (BKv.BloomKv Int String)
genBloomKvIntString = do
  list <- Gen.list (Range.linear 0 10) $ do
    k <- Gen.int (Range.linear 0 100)
    v <- Gen.string (Range.linear 0 10) Gen.alpha
    pure (k, v)
  -- BloomKv.fromList requires a combine function for duplicate keys
  -- We use \_ v -> Just v to keep the second value
  pure $ BKv.fromList (\_ v -> Just v) list

-------------------------------------------------------------------------------
-- Eq Laws
-------------------------------------------------------------------------------

propBloomKvEqReflexivity :: Property
propBloomKvEqReflexivity = H.property $ do
  bkv <- H.forAll genBloomKvIntString
  H.assert $ Helpers.checkEqReflexivity (==) bkv

propBloomKvEqSymmetry :: Property
propBloomKvEqSymmetry = H.property $ do
  bkv1 <- H.forAll genBloomKvIntString
  bkv2 <- H.forAll genBloomKvIntString
  H.assert $ Helpers.checkEqSymmetry (==) (==) bkv1 bkv2

propBloomKvEqTransitivity :: Property
propBloomKvEqTransitivity = H.property $ do
  bkv1 <- H.forAll genBloomKvIntString
  bkv2 <- H.forAll genBloomKvIntString
  bkv3 <- H.forAll genBloomKvIntString
  let eq12 = bkv1 == bkv2
  let eq23 = bkv2 == bkv3
  let eq13 = bkv1 == bkv3
  H.assert $ Helpers.checkEqTransitivity eq12 eq23 eq13

-------------------------------------------------------------------------------
-- Eq1 Consistency
-------------------------------------------------------------------------------

propBloomKvEq1Consistency :: Property
propBloomKvEq1Consistency = H.property $ do
  bkv1 <- H.forAll genBloomKvIntString
  bkv2 <- H.forAll genBloomKvIntString
  liftEq (==) bkv1 bkv2 H.=== (bkv1 == bkv2)

-------------------------------------------------------------------------------
-- Ord Laws
-------------------------------------------------------------------------------

propBloomKvOrdReflexivity :: Property
propBloomKvOrdReflexivity = H.property $ do
  bkv <- H.forAll genBloomKvIntString
  compare bkv bkv H.=== EQ

propBloomKvOrdAntisymmetry :: Property
propBloomKvOrdAntisymmetry = H.property $ do
  bkv1 <- H.forAll genBloomKvIntString
  bkv2 <- H.forAll genBloomKvIntString
  let ord1 = compare bkv1 bkv2
  let ord2 = compare bkv2 bkv1
  H.assert $ Helpers.checkOrdAntisymmetry ord1 ord2

propBloomKvOrdTransitivity :: Property
propBloomKvOrdTransitivity = H.property $ do
  bkv1 <- H.forAll genBloomKvIntString
  bkv2 <- H.forAll genBloomKvIntString
  bkv3 <- H.forAll genBloomKvIntString
  let ord12 = compare bkv1 bkv2
  let ord23 = compare bkv2 bkv3
  let ord13 = compare bkv1 bkv3
  H.assert $ Helpers.checkOrdTransitivity ord12 ord23 ord13

propBloomKvOrdEqConsistency :: Property
propBloomKvOrdEqConsistency = H.property $ do
  bkv1 <- H.forAll genBloomKvIntString
  bkv2 <- H.forAll genBloomKvIntString
  let eq = bkv1 == bkv2
  let ord = compare bkv1 bkv2
  H.assert $ Helpers.checkOrdEqConsistency eq ord

-------------------------------------------------------------------------------
-- Ord1 Consistency
-------------------------------------------------------------------------------

propBloomKvOrd1Consistency :: Property
propBloomKvOrd1Consistency = H.property $ do
  bkv1 <- H.forAll genBloomKvIntString
  bkv2 <- H.forAll genBloomKvIntString
  liftCompare compare bkv1 bkv2 H.=== compare bkv1 bkv2

-------------------------------------------------------------------------------
-- Test Tree
-------------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "Bloom.Kv"
  [ testGroup "Eq Laws"
      [ testProperty "Reflexivity (x == x)" $
          H.withTests 1000 propBloomKvEqReflexivity
      , testProperty "Symmetry (x == y <==> y == x)" $
          H.withTests 1000 propBloomKvEqSymmetry
      , testProperty "Transitivity" $
          H.withTests 1000 propBloomKvEqTransitivity
      ]
  , testGroup "Eq1 Consistency"
      [ testProperty "liftEq (==) behaves like (==)" $
          H.withTests 1000 propBloomKvEq1Consistency
      ]
  , testGroup "Ord Laws"
      [ testProperty "Reflexivity (compare x x == EQ)" $
          H.withTests 1000 propBloomKvOrdReflexivity
      , testProperty "Antisymmetry" $
          H.withTests 1000 propBloomKvOrdAntisymmetry
      , testProperty "Transitivity" $
          H.withTests 1000 propBloomKvOrdTransitivity
      , testProperty "Consistency with Eq" $
          H.withTests 1000 propBloomKvOrdEqConsistency
      ]
  , testGroup "Ord1 Consistency"
      [ testProperty "liftCompare compare behaves like compare" $
          H.withTests 1000 propBloomKvOrd1Consistency
      ]
  ]

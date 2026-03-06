module Who2.Laws.HashConsed.Set (tests) where

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import qualified Who2.Expr.HashConsed.Set as ES
import Who2.Laws.Helpers (MockExpr(MockExpr))
import qualified Who2.Laws.Helpers as Helpers

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

genExprSetInt :: H.Gen (ES.ExprSet MockExpr)
genExprSetInt = do
  list <- Gen.list (Range.linear 0 10) $ MockExpr <$> Gen.int (Range.linear 0 100)
  pure $ ES.fromList list

-------------------------------------------------------------------------------
-- Eq Laws
-------------------------------------------------------------------------------

propExprSetEqReflexivity :: Property
propExprSetEqReflexivity = H.property $ do
  es <- H.forAll genExprSetInt
  H.assert $ Helpers.checkEqReflexivity (==) es

propExprSetEqSymmetry :: Property
propExprSetEqSymmetry = H.property $ do
  es1 <- H.forAll genExprSetInt
  es2 <- H.forAll genExprSetInt
  H.assert $ Helpers.checkEqSymmetry (==) (==) es1 es2

propExprSetEqTransitivity :: Property
propExprSetEqTransitivity = H.property $ do
  es1 <- H.forAll genExprSetInt
  es2 <- H.forAll genExprSetInt
  es3 <- H.forAll genExprSetInt
  let eq12 = es1 == es2
  let eq23 = es2 == es3
  let eq13 = es1 == es3
  H.assert $ Helpers.checkEqTransitivity eq12 eq23 eq13

-------------------------------------------------------------------------------
-- Ord Laws
-------------------------------------------------------------------------------

propExprSetOrdReflexivity :: Property
propExprSetOrdReflexivity = H.property $ do
  es <- H.forAll genExprSetInt
  compare es es H.=== EQ

propExprSetOrdAntisymmetry :: Property
propExprSetOrdAntisymmetry = H.property $ do
  es1 <- H.forAll genExprSetInt
  es2 <- H.forAll genExprSetInt
  let ord1 = compare es1 es2
  let ord2 = compare es2 es1
  H.assert $ Helpers.checkOrdAntisymmetry ord1 ord2

propExprSetOrdTransitivity :: Property
propExprSetOrdTransitivity = H.property $ do
  es1 <- H.forAll genExprSetInt
  es2 <- H.forAll genExprSetInt
  es3 <- H.forAll genExprSetInt
  let ord12 = compare es1 es2
  let ord23 = compare es2 es3
  let ord13 = compare es1 es3
  H.assert $ Helpers.checkOrdTransitivity ord12 ord23 ord13

propExprSetOrdEqConsistency :: Property
propExprSetOrdEqConsistency = H.property $ do
  es1 <- H.forAll genExprSetInt
  es2 <- H.forAll genExprSetInt
  let eq = es1 == es2
  let ord = compare es1 es2
  H.assert $ Helpers.checkOrdEqConsistency eq ord

-------------------------------------------------------------------------------
-- Test Tree
-------------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "HashConsed.ExprSet"
  [ testGroup "Eq Laws"
      [ testProperty "Reflexivity (x == x)" $
          H.withTests 1000 propExprSetEqReflexivity
      , testProperty "Symmetry (x == y <==> y == x)" $
          H.withTests 1000 propExprSetEqSymmetry
      , testProperty "Transitivity" $
          H.withTests 1000 propExprSetEqTransitivity
      ]
  , testGroup "Ord Laws"
      [ testProperty "Reflexivity (compare x x == EQ)" $
          H.withTests 1000 propExprSetOrdReflexivity
      , testProperty "Antisymmetry" $
          H.withTests 1000 propExprSetOrdAntisymmetry
      , testProperty "Transitivity" $
          H.withTests 1000 propExprSetOrdTransitivity
      , testProperty "Consistency with Eq" $
          H.withTests 1000 propExprSetOrdEqConsistency
      ]
  ]

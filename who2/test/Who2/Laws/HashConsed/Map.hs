module Who2.Laws.HashConsed.Map (tests) where

import Data.Functor.Classes (Eq1(liftEq), Ord1(liftCompare))

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import qualified Who2.Expr.HashConsed.Map as EM
import Who2.Laws.Helpers (MockExpr(MockExpr))
import qualified Who2.Laws.Helpers as Helpers

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

genExprMapIntString :: H.Gen (EM.ExprMap MockExpr String)
genExprMapIntString = do
  list <- Gen.list (Range.linear 0 10) $ do
    k <- MockExpr <$> Gen.int (Range.linear 0 100)
    v <- Gen.string (Range.linear 0 10) Gen.alpha
    pure (k, v)
  pure $ foldr (\(k, v) m -> EM.insert k v m) EM.empty list

-------------------------------------------------------------------------------
-- Eq Laws
-------------------------------------------------------------------------------

propExprMapEqReflexivity :: Property
propExprMapEqReflexivity = H.property $ do
  em <- H.forAll genExprMapIntString
  H.assert $ Helpers.checkEqReflexivity (==) em

propExprMapEqSymmetry :: Property
propExprMapEqSymmetry = H.property $ do
  em1 <- H.forAll genExprMapIntString
  em2 <- H.forAll genExprMapIntString
  H.assert $ Helpers.checkEqSymmetry (==) (==) em1 em2

propExprMapEqTransitivity :: Property
propExprMapEqTransitivity = H.property $ do
  em1 <- H.forAll genExprMapIntString
  em2 <- H.forAll genExprMapIntString
  em3 <- H.forAll genExprMapIntString
  let eq12 = em1 == em2
  let eq23 = em2 == em3
  let eq13 = em1 == em3
  H.assert $ Helpers.checkEqTransitivity eq12 eq23 eq13

-------------------------------------------------------------------------------
-- Eq1 Consistency
-------------------------------------------------------------------------------

propExprMapEq1Consistency :: Property
propExprMapEq1Consistency = H.property $ do
  em1 <- H.forAll genExprMapIntString
  em2 <- H.forAll genExprMapIntString
  liftEq (==) em1 em2 H.=== (em1 == em2)

-------------------------------------------------------------------------------
-- Ord Laws
-------------------------------------------------------------------------------

propExprMapOrdReflexivity :: Property
propExprMapOrdReflexivity = H.property $ do
  em <- H.forAll genExprMapIntString
  compare em em H.=== EQ

propExprMapOrdAntisymmetry :: Property
propExprMapOrdAntisymmetry = H.property $ do
  em1 <- H.forAll genExprMapIntString
  em2 <- H.forAll genExprMapIntString
  let ord1 = compare em1 em2
  let ord2 = compare em2 em1
  H.assert $ Helpers.checkOrdAntisymmetry ord1 ord2

propExprMapOrdTransitivity :: Property
propExprMapOrdTransitivity = H.property $ do
  em1 <- H.forAll genExprMapIntString
  em2 <- H.forAll genExprMapIntString
  em3 <- H.forAll genExprMapIntString
  let ord12 = compare em1 em2
  let ord23 = compare em2 em3
  let ord13 = compare em1 em3
  H.assert $ Helpers.checkOrdTransitivity ord12 ord23 ord13

propExprMapOrdEqConsistency :: Property
propExprMapOrdEqConsistency = H.property $ do
  em1 <- H.forAll genExprMapIntString
  em2 <- H.forAll genExprMapIntString
  let eq = em1 == em2
  let ord = compare em1 em2
  H.assert $ Helpers.checkOrdEqConsistency eq ord

-------------------------------------------------------------------------------
-- Ord1 Consistency
-------------------------------------------------------------------------------

propExprMapOrd1Consistency :: Property
propExprMapOrd1Consistency = H.property $ do
  em1 <- H.forAll genExprMapIntString
  em2 <- H.forAll genExprMapIntString
  liftCompare compare em1 em2 H.=== compare em1 em2

-------------------------------------------------------------------------------
-- Test Tree
-------------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "HashConsed.ExprMap"
  [ testGroup "Eq Laws"
      [ testProperty "Reflexivity (x == x)" $
          H.withTests 1000 propExprMapEqReflexivity
      , testProperty "Symmetry (x == y <==> y == x)" $
          H.withTests 1000 propExprMapEqSymmetry
      , testProperty "Transitivity" $
          H.withTests 1000 propExprMapEqTransitivity
      ]
  , testGroup "Eq1 Consistency"
      [ testProperty "liftEq (==) behaves like (==)" $
          H.withTests 1000 propExprMapEq1Consistency
      ]
  , testGroup "Ord Laws"
      [ testProperty "Reflexivity (compare x x == EQ)" $
          H.withTests 1000 propExprMapOrdReflexivity
      , testProperty "Antisymmetry" $
          H.withTests 1000 propExprMapOrdAntisymmetry
      , testProperty "Transitivity" $
          H.withTests 1000 propExprMapOrdTransitivity
      , testProperty "Consistency with Eq" $
          H.withTests 1000 propExprMapOrdEqConsistency
      ]
  , testGroup "Ord1 Consistency"
      [ testProperty "liftCompare compare behaves like compare" $
          H.withTests 1000 propExprMapOrd1Consistency
      ]
  ]

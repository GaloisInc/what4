module Who2.Laws.HashConsed.Polarized (tests) where

import Control.Monad (unless)
import Data.Hashable (hash)

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import qualified Who2.Expr.HashConsed.Polarized as PES
import qualified Who2.Expr.HashConsed.Set as ES
import Who2.Laws.Helpers (MockExpr(MockExpr))
import qualified Who2.Laws.Helpers as Helpers

genPolarizedExprSet :: H.Gen (PES.PolarizedExprSet MockExpr)
genPolarizedExprSet = do
  posElems <- Gen.list (Range.linear 0 5) $ MockExpr <$> Gen.int (Range.linear 1 100)
  negElems <- Gen.list (Range.linear 0 5) $ MockExpr <$> Gen.int (Range.linear 1 100)
  let posSet = ES.fromList posElems
  let negSet = ES.fromList negElems
  pure $ PES.PolarizedExprSet posSet negSet

-------------------------------------------------------------------------------
-- Eq Laws
-------------------------------------------------------------------------------

propPolarizedExprSetEqReflexivity :: Property
propPolarizedExprSetEqReflexivity = H.property $ do
  pes <- H.forAll genPolarizedExprSet
  H.assert $ Helpers.checkEqReflexivity (==) pes

propPolarizedExprSetEqSymmetry :: Property
propPolarizedExprSetEqSymmetry = H.property $ do
  pes1 <- H.forAll genPolarizedExprSet
  pes2 <- H.forAll genPolarizedExprSet
  H.assert $ Helpers.checkEqSymmetry (==) (==) pes1 pes2

propPolarizedExprSetEqTransitivity :: Property
propPolarizedExprSetEqTransitivity = H.property $ do
  pes1 <- H.forAll genPolarizedExprSet
  pes2 <- H.forAll genPolarizedExprSet
  pes3 <- H.forAll genPolarizedExprSet
  let eq12 = pes1 == pes2
  let eq23 = pes2 == pes3
  let eq13 = pes1 == pes3
  H.assert $ Helpers.checkEqTransitivity eq12 eq23 eq13

-------------------------------------------------------------------------------
-- Hashable Laws
-------------------------------------------------------------------------------

-- | PolarizedExprSet Eq/Hashable consistency: equal sets have equal hashes
propPolarizedExprSetEqHashConsistency :: Property
propPolarizedExprSetEqHashConsistency = H.property $ do
  pes1 <- H.forAll genPolarizedExprSet
  pes2 <- H.forAll genPolarizedExprSet
  unless (pes1 == pes2) H.discard
  hash pes1 H.=== hash pes2

-------------------------------------------------------------------------------
-- Test Tree
-------------------------------------------------------------------------------

tests :: TestTree
tests = testGroup "HashConsed.PolarizedExprSet"
  [ testGroup "Eq Laws"
      [ testProperty "Reflexivity (x == x)" $
          H.withTests 1000 propPolarizedExprSetEqReflexivity
      , testProperty "Symmetry (x == y <==> y == x)" $
          H.withTests 1000 propPolarizedExprSetEqSymmetry
      , testProperty "Transitivity" $
          H.withTests 1000 propPolarizedExprSetEqTransitivity
      ]
  , testGroup "Hashable Laws"
      [ testProperty "Consistency with Eq (equal implies same hash)" $
          H.withTests 1000 $ H.withDiscards 10000 propPolarizedExprSetEqHashConsistency
      ]
  ]

module Who2.Laws.HashConsed.Set
  ( -- Eq properties
    propExprSetEqReflexive
  , propExprSetEqSymmetric
  , propExprSetEqTransitive
  -- Ord properties
  , propExprSetOrdReflexive
  , propExprSetOrdAntisymmetric
  , propExprSetOrdTransitive
  , propExprSetOrdConsistentWithEq
  ) where

import Control.Monad (unless)

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Who2.Expr.HashConsed.Set as ES
import Who2.Laws.Helpers (MockExpr(..), checkOrdTransitivity, checkOrdAntisymmetry)

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

genExprSetInt :: H.Gen (ES.ExprSet MockExpr)
genExprSetInt = do
  list <- Gen.list (Range.linear 0 10) $ MockExpr <$> Gen.int (Range.linear 0 100)
  pure $ ES.fromList list

-------------------------------------------------------------------------------
-- Eq Properties
-------------------------------------------------------------------------------

propExprSetEqReflexive :: Property
propExprSetEqReflexive = H.property $ do
  es <- H.forAll genExprSetInt
  H.assert $ es == es

propExprSetEqSymmetric :: Property
propExprSetEqSymmetric = H.property $ do
  es1 <- H.forAll genExprSetInt
  es2 <- H.forAll genExprSetInt
  let eq1 = es1 == es2
  let eq2 = es2 == es1
  eq1 H.=== eq2

propExprSetEqTransitive :: Property
propExprSetEqTransitive = H.property $ do
  es1 <- H.forAll genExprSetInt
  es2 <- H.forAll genExprSetInt
  es3 <- H.forAll genExprSetInt
  let eq12 = es1 == es2
  let eq23 = es2 == es3
  let eq13 = es1 == es3
  unless (not eq12 || not eq23 || eq13) H.failure

-------------------------------------------------------------------------------
-- Ord Properties
-------------------------------------------------------------------------------

propExprSetOrdReflexive :: Property
propExprSetOrdReflexive = H.property $ do
  es <- H.forAll genExprSetInt
  compare es es H.=== EQ

propExprSetOrdAntisymmetric :: Property
propExprSetOrdAntisymmetric = H.property $ do
  es1 <- H.forAll genExprSetInt
  es2 <- H.forAll genExprSetInt
  let ord1 = compare es1 es2
  let ord2 = compare es2 es1
  unless (checkOrdAntisymmetry ord1 ord2) H.failure

propExprSetOrdTransitive :: Property
propExprSetOrdTransitive = H.property $ do
  es1 <- H.forAll genExprSetInt
  es2 <- H.forAll genExprSetInt
  es3 <- H.forAll genExprSetInt
  let ord12 = compare es1 es2
  let ord23 = compare es2 es3
  let ord13 = compare es1 es3
  unless (checkOrdTransitivity ord12 ord23 ord13) H.failure

propExprSetOrdConsistentWithEq :: Property
propExprSetOrdConsistentWithEq = H.property $ do
  es1 <- H.forAll genExprSetInt
  es2 <- H.forAll genExprSetInt
  let eq = es1 == es2
  let ord = compare es1 es2
  let result = case (eq, ord) of
        (True, EQ) -> True
        (False, LT) -> True
        (False, GT) -> True
        (True, LT) -> False
        (True, GT) -> False
        (False, EQ) -> False
  unless result H.failure

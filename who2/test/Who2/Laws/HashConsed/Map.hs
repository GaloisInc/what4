module Who2.Laws.HashConsed.Map
  ( -- eqBy properties
    propExprMapEqByReflexive
  , propExprMapEqBySymmetric
  , propExprMapEqByTransitive
  -- ordBy properties
  , propExprMapOrdByReflexive
  , propExprMapOrdByAntisymmetric
  , propExprMapOrdByTransitive
  , propExprMapOrdByConsistentWithEqBy
  ) where

import Control.Monad (unless)
import Data.Functor.Classes (Eq1(liftEq), Ord1(liftCompare))

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Who2.Expr.HashConsed.Map as EM
import Who2.Laws.Helpers (MockExpr(..), checkOrdTransitivity, checkOrdAntisymmetry)

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
-- eqBy Properties
-------------------------------------------------------------------------------

propExprMapEqByReflexive :: Property
propExprMapEqByReflexive = H.property $ do
  em <- H.forAll genExprMapIntString
  H.assert $ liftEq (==) em em

propExprMapEqBySymmetric :: Property
propExprMapEqBySymmetric = H.property $ do
  em1 <- H.forAll genExprMapIntString
  em2 <- H.forAll genExprMapIntString
  let eq1 = liftEq (==) em1 em2
  let eq2 = liftEq (==) em2 em1
  eq1 H.=== eq2

propExprMapEqByTransitive :: Property
propExprMapEqByTransitive = H.property $ do
  em1 <- H.forAll genExprMapIntString
  em2 <- H.forAll genExprMapIntString
  em3 <- H.forAll genExprMapIntString
  let eq12 = liftEq (==) em1 em2
  let eq23 = liftEq (==) em2 em3
  let eq13 = liftEq (==) em1 em3
  unless (not eq12 || not eq23 || eq13) H.failure

-------------------------------------------------------------------------------
-- ordBy Properties
-------------------------------------------------------------------------------

propExprMapOrdByReflexive :: Property
propExprMapOrdByReflexive = H.property $ do
  em <- H.forAll genExprMapIntString
  liftCompare compare em em H.=== EQ

propExprMapOrdByAntisymmetric :: Property
propExprMapOrdByAntisymmetric = H.property $ do
  em1 <- H.forAll genExprMapIntString
  em2 <- H.forAll genExprMapIntString
  let ord1 = liftCompare compare em1 em2
  let ord2 = liftCompare compare em2 em1
  unless (checkOrdAntisymmetry ord1 ord2) H.failure

propExprMapOrdByTransitive :: Property
propExprMapOrdByTransitive = H.property $ do
  em1 <- H.forAll genExprMapIntString
  em2 <- H.forAll genExprMapIntString
  em3 <- H.forAll genExprMapIntString
  let ord12 = liftCompare compare em1 em2
  let ord23 = liftCompare compare em2 em3
  let ord13 = liftCompare compare em1 em3
  unless (checkOrdTransitivity ord12 ord23 ord13) H.failure

propExprMapOrdByConsistentWithEqBy :: Property
propExprMapOrdByConsistentWithEqBy = H.property $ do
  em1 <- H.forAll genExprMapIntString
  em2 <- H.forAll genExprMapIntString
  let eq = liftEq (==) em1 em2
  let ord = liftCompare compare em1 em2
  let result = case (eq, ord) of
        (True, EQ) -> True
        (False, LT) -> True
        (False, GT) -> True
        (True, LT) -> False
        (True, GT) -> False
        (False, EQ) -> False
  unless result H.failure

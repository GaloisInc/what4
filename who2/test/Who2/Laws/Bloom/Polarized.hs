module Who2.Laws.Bloom.Polarized
  ( -- eqBy properties
    propPolarizedBloomSeqEqByReflexive
  , propPolarizedBloomSeqEqBySymmetric
  , propPolarizedBloomSeqEqByTransitive
  -- ordBy properties
  , propPolarizedBloomSeqOrdByReflexive
  , propPolarizedBloomSeqOrdByAntisymmetric
  , propPolarizedBloomSeqOrdByTransitive
  , propPolarizedBloomSeqOrdByConsistentWithEqBy
  ) where

import Control.Monad (unless)
import Data.Functor.Classes (Eq1(liftEq), Ord1(liftCompare))

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Who2.Expr.Bloom.Polarized as PBS
import Who2.Laws.Helpers (checkOrdTransitivity, checkOrdAntisymmetry)

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
-- eqBy Properties
-------------------------------------------------------------------------------

propPolarizedBloomSeqEqByReflexive :: Property
propPolarizedBloomSeqEqByReflexive = H.property $ do
  pbs <- H.forAll genPolarizedBloomSeqInt
  H.assert $ liftEq (==) pbs pbs

propPolarizedBloomSeqEqBySymmetric :: Property
propPolarizedBloomSeqEqBySymmetric = H.property $ do
  pbs1 <- H.forAll genPolarizedBloomSeqInt
  pbs2 <- H.forAll genPolarizedBloomSeqInt
  let eq1 = liftEq (==) pbs1 pbs2
  let eq2 = liftEq (==) pbs2 pbs1
  eq1 H.=== eq2

propPolarizedBloomSeqEqByTransitive :: Property
propPolarizedBloomSeqEqByTransitive = H.property $ do
  pbs1 <- H.forAll genPolarizedBloomSeqInt
  pbs2 <- H.forAll genPolarizedBloomSeqInt
  pbs3 <- H.forAll genPolarizedBloomSeqInt
  let eq12 = liftEq (==) pbs1 pbs2
  let eq23 = liftEq (==) pbs2 pbs3
  let eq13 = liftEq (==) pbs1 pbs3
  unless (not eq12 || not eq23 || eq13) H.failure

-------------------------------------------------------------------------------
-- ordBy Properties
-------------------------------------------------------------------------------

propPolarizedBloomSeqOrdByReflexive :: Property
propPolarizedBloomSeqOrdByReflexive = H.property $ do
  pbs <- H.forAll genPolarizedBloomSeqInt
  liftCompare compare pbs pbs H.=== EQ

propPolarizedBloomSeqOrdByAntisymmetric :: Property
propPolarizedBloomSeqOrdByAntisymmetric = H.property $ do
  pbs1 <- H.forAll genPolarizedBloomSeqInt
  pbs2 <- H.forAll genPolarizedBloomSeqInt
  let ord1 = liftCompare compare pbs1 pbs2
  let ord2 = liftCompare compare pbs2 pbs1
  unless (checkOrdAntisymmetry ord1 ord2) H.failure

propPolarizedBloomSeqOrdByTransitive :: Property
propPolarizedBloomSeqOrdByTransitive = H.property $ do
  pbs1 <- H.forAll genPolarizedBloomSeqInt
  pbs2 <- H.forAll genPolarizedBloomSeqInt
  pbs3 <- H.forAll genPolarizedBloomSeqInt
  let ord12 = liftCompare compare pbs1 pbs2
  let ord23 = liftCompare compare pbs2 pbs3
  let ord13 = liftCompare compare pbs1 pbs3
  unless (checkOrdTransitivity ord12 ord23 ord13) H.failure

propPolarizedBloomSeqOrdByConsistentWithEqBy :: Property
propPolarizedBloomSeqOrdByConsistentWithEqBy = H.property $ do
  pbs1 <- H.forAll genPolarizedBloomSeqInt
  pbs2 <- H.forAll genPolarizedBloomSeqInt
  let eq = liftEq (==) pbs1 pbs2
  let ord = liftCompare compare pbs1 pbs2
  let result = case (eq, ord) of
        (True, EQ) -> True
        (False, LT) -> True
        (False, GT) -> True
        (True, LT) -> False
        (True, GT) -> False
        (False, EQ) -> False
  unless result H.failure

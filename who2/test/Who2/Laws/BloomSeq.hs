module Who2.Laws.BloomSeq
  ( -- eqBy properties
    propBloomSeqEqByReflexive
  , propBloomSeqEqBySymmetric
  , propBloomSeqEqByTransitive
  -- ordBy properties
  , propBloomSeqOrdByReflexive
  , propBloomSeqOrdByAntisymmetric
  , propBloomSeqOrdByTransitive
  , propBloomSeqOrdByConsistentWithEqBy
  ) where

import Control.Monad (unless)

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Who2.Expr.Bloom.Seq as BS
import Who2.Laws.Helpers (checkOrdTransitivity, checkOrdAntisymmetry)

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

genBloomSeqInt :: H.Gen (BS.BloomSeq Int)
genBloomSeqInt = do
  list <- Gen.list (Range.linear 0 10) (Gen.int (Range.linear 0 100))
  pure $ BS.fromList list

-------------------------------------------------------------------------------
-- eqBy Properties
-------------------------------------------------------------------------------

propBloomSeqEqByReflexive :: Property
propBloomSeqEqByReflexive = H.property $ do
  bs <- H.forAll genBloomSeqInt
  H.assert $ BS.eqBy (==) bs bs

propBloomSeqEqBySymmetric :: Property
propBloomSeqEqBySymmetric = H.property $ do
  bs1 <- H.forAll genBloomSeqInt
  bs2 <- H.forAll genBloomSeqInt
  let eq1 = BS.eqBy (==) bs1 bs2
  let eq2 = BS.eqBy (==) bs2 bs1
  eq1 H.=== eq2

propBloomSeqEqByTransitive :: Property
propBloomSeqEqByTransitive = H.property $ do
  bs1 <- H.forAll genBloomSeqInt
  bs2 <- H.forAll genBloomSeqInt
  bs3 <- H.forAll genBloomSeqInt
  let eq12 = BS.eqBy (==) bs1 bs2
  let eq23 = BS.eqBy (==) bs2 bs3
  let eq13 = BS.eqBy (==) bs1 bs3
  unless (not eq12 || not eq23 || eq13) H.failure

-------------------------------------------------------------------------------
-- ordBy Properties
-------------------------------------------------------------------------------

propBloomSeqOrdByReflexive :: Property
propBloomSeqOrdByReflexive = H.property $ do
  bs <- H.forAll genBloomSeqInt
  BS.ordBy compare bs bs H.=== EQ

propBloomSeqOrdByAntisymmetric :: Property
propBloomSeqOrdByAntisymmetric = H.property $ do
  bs1 <- H.forAll genBloomSeqInt
  bs2 <- H.forAll genBloomSeqInt
  let ord1 = BS.ordBy compare bs1 bs2
  let ord2 = BS.ordBy compare bs2 bs1
  unless (checkOrdAntisymmetry ord1 ord2) H.failure

propBloomSeqOrdByTransitive :: Property
propBloomSeqOrdByTransitive = H.property $ do
  bs1 <- H.forAll genBloomSeqInt
  bs2 <- H.forAll genBloomSeqInt
  bs3 <- H.forAll genBloomSeqInt
  let ord12 = BS.ordBy compare bs1 bs2
  let ord23 = BS.ordBy compare bs2 bs3
  let ord13 = BS.ordBy compare bs1 bs3
  unless (checkOrdTransitivity ord12 ord23 ord13) H.failure

propBloomSeqOrdByConsistentWithEqBy :: Property
propBloomSeqOrdByConsistentWithEqBy = H.property $ do
  bs1 <- H.forAll genBloomSeqInt
  bs2 <- H.forAll genBloomSeqInt
  let eq = BS.eqBy (==) bs1 bs2
  let ord = BS.ordBy compare bs1 bs2
  let result = case (eq, ord) of
        (True, EQ) -> True
        (False, LT) -> True
        (False, GT) -> True
        _ -> False
  unless result H.failure

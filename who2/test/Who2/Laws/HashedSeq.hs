module Who2.Laws.HashedSeq
  ( -- ordBy properties (no eqBy in HashedSeq)
    propHashedSeqOrdByReflexive
  , propHashedSeqOrdByAntisymmetric
  , propHashedSeqOrdByTransitive
  ) where

import Control.Monad (unless)

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Who2.Expr.Bloom.HashedSeq as HS
import Who2.Laws.Helpers (checkOrdTransitivity, checkOrdAntisymmetry)

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

genHashedSeqInt :: H.Gen (HS.HashedSeq Int)
genHashedSeqInt = do
  list <- Gen.list (Range.linear 0 10) (Gen.int (Range.linear 0 100))
  pure $ HS.fromList list

-------------------------------------------------------------------------------
-- ordBy Properties
-------------------------------------------------------------------------------

propHashedSeqOrdByReflexive :: Property
propHashedSeqOrdByReflexive = H.property $ do
  hs <- H.forAll genHashedSeqInt
  HS.ordBy compare hs hs H.=== EQ

propHashedSeqOrdByAntisymmetric :: Property
propHashedSeqOrdByAntisymmetric = H.property $ do
  hs1 <- H.forAll genHashedSeqInt
  hs2 <- H.forAll genHashedSeqInt
  let ord1 = HS.ordBy compare hs1 hs2
  let ord2 = HS.ordBy compare hs2 hs1
  unless (checkOrdAntisymmetry ord1 ord2) H.failure

propHashedSeqOrdByTransitive :: Property
propHashedSeqOrdByTransitive = H.property $ do
  hs1 <- H.forAll genHashedSeqInt
  hs2 <- H.forAll genHashedSeqInt
  hs3 <- H.forAll genHashedSeqInt
  let ord12 = HS.ordBy compare hs1 hs2
  let ord23 = HS.ordBy compare hs2 hs3
  let ord13 = HS.ordBy compare hs1 hs3
  unless (checkOrdTransitivity ord12 ord23 ord13) H.failure

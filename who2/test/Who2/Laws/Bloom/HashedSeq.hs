module Who2.Laws.Bloom.HashedSeq
  ( -- Eq and Hash properties
    propHashedSeqHashConsistency
  , propHashedSeqEqConsistency
  , propHashedSeqAppendHashConsistency
  , propHashedSeqMergeHashConsistency
    -- ordBy properties (no eqBy in HashedSeq)
  , propHashedSeqOrdByReflexive
  , propHashedSeqOrdByAntisymmetric
  , propHashedSeqOrdByTransitive
  ) where

import Control.Monad (unless, when)

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Data.Functor.Classes (Ord1(liftCompare))
import Data.Hashable (hash)

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
-- Eq and Hash Properties
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
-- ordBy Properties
-------------------------------------------------------------------------------

propHashedSeqOrdByReflexive :: Property
propHashedSeqOrdByReflexive = H.property $ do
  hs <- H.forAll genHashedSeqInt
  liftCompare compare hs hs H.=== EQ

propHashedSeqOrdByAntisymmetric :: Property
propHashedSeqOrdByAntisymmetric = H.property $ do
  hs1 <- H.forAll genHashedSeqInt
  hs2 <- H.forAll genHashedSeqInt
  let ord1 = liftCompare compare hs1 hs2
  let ord2 = liftCompare compare hs2 hs1
  unless (checkOrdAntisymmetry ord1 ord2) H.failure

propHashedSeqOrdByTransitive :: Property
propHashedSeqOrdByTransitive = H.property $ do
  hs1 <- H.forAll genHashedSeqInt
  hs2 <- H.forAll genHashedSeqInt
  hs3 <- H.forAll genHashedSeqInt
  let ord12 = liftCompare compare hs1 hs2
  let ord23 = liftCompare compare hs2 hs3
  let ord13 = liftCompare compare hs1 hs3
  unless (checkOrdTransitivity ord12 ord23 ord13) H.failure

{-# LANGUAGE ScopedTypeVariables #-}

module Who2.HashedSeq
  ( propHashedSeqHashConsistency
  , propHashedSeqEqConsistency
  , propHashedSeqAppendHashConsistency
  , propHashedSeqMergeHashConsistency
  , propHashedSeqOrdByReflexive
  , propHashedSeqOrdByAntisymmetric
  , propHashedSeqOrdByTransitive
  ) where

import Control.Monad (unless, when)

import Data.Hashable (hash)
import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Who2.Expr.HashedSequence as HS

genHashedSeqInt :: H.Gen (HS.HashedSeq Int)
genHashedSeqInt = do
  list <- Gen.list (Range.linear 0 10) (Gen.int (Range.linear 0 100))
  pure $ HS.fromList list

-- | HashedSeq should maintain hash consistency: equal sequences have equal hashes
propHashedSeqHashConsistency :: Property
propHashedSeqHashConsistency = H.property $ do
  hs1 <- H.forAll genHashedSeqInt
  hs2 <- H.forAll genHashedSeqInt
  when (hs1 == hs2) $ do
    HS.hsHash hs1 H.=== HS.hsHash hs2
    hash hs1 H.=== hash hs2

-- | HashedSeq Eq instance should be consistent
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
  HS.hsHash hs' H.=== HS.hsHash fromList

-- | HashedSeq merge (><) should maintain hash consistency
propHashedSeqMergeHashConsistency :: Property
propHashedSeqMergeHashConsistency = H.property $ do
  hs1 <- H.forAll genHashedSeqInt
  hs2 <- H.forAll genHashedSeqInt
  let hs' = hs1 HS.>< hs2
  let fromList = HS.fromList (HS.toList hs1 ++ HS.toList hs2)
  hs' H.=== fromList
  HS.hsHash hs' H.=== HS.hsHash fromList

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
  let result = case (ord1, ord2) of
        (LT, GT) -> True
        (EQ, EQ) -> True
        (GT, LT) -> True
        _ -> False
  unless result H.failure

propHashedSeqOrdByTransitive :: Property
propHashedSeqOrdByTransitive = H.property $ do
  hs1 <- H.forAll genHashedSeqInt
  hs2 <- H.forAll genHashedSeqInt
  hs3 <- H.forAll genHashedSeqInt
  let ord12 = HS.ordBy compare hs1 hs2
  let ord23 = HS.ordBy compare hs2 hs3
  let ord13 = HS.ordBy compare hs1 hs3
  let result = case (ord12, ord23, ord13) of
        (LT, LT, LT) -> True
        (LT, LT, _) -> False
        (LT, EQ, LT) -> True
        (LT, EQ, _) -> False
        (EQ, LT, LT) -> True
        (EQ, LT, _) -> False
        (GT, GT, GT) -> True
        (GT, GT, _) -> False
        (GT, EQ, GT) -> True
        (GT, EQ, _) -> False
        (EQ, GT, GT) -> True
        (EQ, GT, _) -> False
        (EQ, EQ, EQ) -> True
        (EQ, EQ, _) -> False
        (LT, GT, _) -> True
        (GT, LT, _) -> True
  unless result H.failure

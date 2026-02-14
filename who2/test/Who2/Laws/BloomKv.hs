module Who2.Laws.BloomKv
  ( -- eqBy properties
    propBloomKvEqByReflexive
  , propBloomKvEqBySymmetric
  , propBloomKvEqByTransitive
  -- ordBy properties
  , propBloomKvOrdByReflexive
  , propBloomKvOrdByAntisymmetric
  , propBloomKvOrdByTransitive
  , propBloomKvOrdByConsistentWithEqBy
  ) where

import Control.Monad (unless)
import Data.Functor.Classes (Eq1(liftEq), Ord1(liftCompare))

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Who2.Expr.Bloom.Kv as BKv
import Who2.Laws.Helpers (checkOrdTransitivity, checkOrdAntisymmetry)

-------------------------------------------------------------------------------
-- Generator
-------------------------------------------------------------------------------

genBloomKvIntString :: H.Gen (BKv.BloomKv Int String)
genBloomKvIntString = do
  list <- Gen.list (Range.linear 0 10) $ do
    k <- Gen.int (Range.linear 0 100)
    v <- Gen.string (Range.linear 0 10) Gen.alpha
    pure (k, v)
  -- BloomKv.fromList requires a combine function for duplicate keys
  -- We use const to keep the second value
  pure $ BKv.fromList const list

-------------------------------------------------------------------------------
-- eqBy Properties
-------------------------------------------------------------------------------

propBloomKvEqByReflexive :: Property
propBloomKvEqByReflexive = H.property $ do
  bkv <- H.forAll genBloomKvIntString
  H.assert $ liftEq (==) bkv bkv

propBloomKvEqBySymmetric :: Property
propBloomKvEqBySymmetric = H.property $ do
  bkv1 <- H.forAll genBloomKvIntString
  bkv2 <- H.forAll genBloomKvIntString
  let eq1 = liftEq (==) bkv1 bkv2
  let eq2 = liftEq (==) bkv2 bkv1
  eq1 H.=== eq2

propBloomKvEqByTransitive :: Property
propBloomKvEqByTransitive = H.property $ do
  bkv1 <- H.forAll genBloomKvIntString
  bkv2 <- H.forAll genBloomKvIntString
  bkv3 <- H.forAll genBloomKvIntString
  let eq12 = liftEq (==) bkv1 bkv2
  let eq23 = liftEq (==) bkv2 bkv3
  let eq13 = liftEq (==) bkv1 bkv3
  unless (not eq12 || not eq23 || eq13) H.failure

-------------------------------------------------------------------------------
-- ordBy Properties
-------------------------------------------------------------------------------

propBloomKvOrdByReflexive :: Property
propBloomKvOrdByReflexive = H.property $ do
  bkv <- H.forAll genBloomKvIntString
  liftCompare compare bkv bkv H.=== EQ

propBloomKvOrdByAntisymmetric :: Property
propBloomKvOrdByAntisymmetric = H.property $ do
  bkv1 <- H.forAll genBloomKvIntString
  bkv2 <- H.forAll genBloomKvIntString
  let ord1 = liftCompare compare bkv1 bkv2
  let ord2 = liftCompare compare bkv2 bkv1
  unless (checkOrdAntisymmetry ord1 ord2) H.failure

propBloomKvOrdByTransitive :: Property
propBloomKvOrdByTransitive = H.property $ do
  bkv1 <- H.forAll genBloomKvIntString
  bkv2 <- H.forAll genBloomKvIntString
  bkv3 <- H.forAll genBloomKvIntString
  let ord12 = liftCompare compare bkv1 bkv2
  let ord23 = liftCompare compare bkv2 bkv3
  let ord13 = liftCompare compare bkv1 bkv3
  unless (checkOrdTransitivity ord12 ord23 ord13) H.failure

propBloomKvOrdByConsistentWithEqBy :: Property
propBloomKvOrdByConsistentWithEqBy = H.property $ do
  bkv1 <- H.forAll genBloomKvIntString
  bkv2 <- H.forAll genBloomKvIntString
  let eq = liftEq (==) bkv1 bkv2
  let ord = liftCompare compare bkv1 bkv2
  let result = case (eq, ord) of
        (True, EQ) -> True
        (False, LT) -> True
        (False, GT) -> True
        _ -> False
  unless result H.failure

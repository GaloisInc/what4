module Who2.Laws.Bloom.Filter
  ( -- Basic Filter properties
    propFilterEmptyMightNotContain
  , propFilterInsertMightContain
  , propFilterDisjointEmpty
  , propFilterUnionContains
  ) where

import Hedgehog (Property)
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Who2.Expr.Bloom.Filter as Filt

-------------------------------------------------------------------------------
-- Basic Filter Properties
-------------------------------------------------------------------------------

-- | Empty filter should not contain any elements (unless disabled)
propFilterEmptyMightNotContain :: Property
propFilterEmptyMightNotContain = H.property $ do
  x <- H.forAll $ Gen.int (Range.linear 0 1000)
  let filt = Filt.empty :: Filt.Filter Int
  -- If the filter is disabled, it will contain everything
  -- Otherwise it should not contain x
  if filt == Filt.disabled
    then H.assert $ Filt.mightContain filt x
    else H.assert $ not (Filt.mightContain filt x)

-- | After inserting an element, filter should report it might contain it
propFilterInsertMightContain :: Property
propFilterInsertMightContain = H.property $ do
  x <- H.forAll $ Gen.int (Range.linear 0 1000)
  let filt = Filt.insert Filt.empty x
  H.assert $ Filt.mightContain filt x

-- | Empty filters should be disjoint (unless disabled)
propFilterDisjointEmpty :: Property
propFilterDisjointEmpty = H.property $ do
  let filt1 = Filt.empty :: Filt.Filter Int
  let filt2 = Filt.empty :: Filt.Filter Int
  if filt1 == Filt.disabled
    then H.assert $ not (Filt.disjoint filt1 filt2)
    else H.assert $ Filt.disjoint filt1 filt2

-- | Union of filters should contain elements from both
propFilterUnionContains :: Property
propFilterUnionContains = H.property $ do
  x <- H.forAll $ Gen.int (Range.linear 0 1000)
  y <- H.forAll $ Gen.int (Range.linear 0 1000)
  let filt1 = Filt.insert Filt.empty x
  let filt2 = Filt.insert Filt.empty y
  let union = Filt.union filt1 filt2
  H.assert $ Filt.mightContain union x
  H.assert $ Filt.mightContain union y

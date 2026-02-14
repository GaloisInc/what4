{-# LANGUAGE StrictData #-}

-- | Bloom filter for fast negative membership tests
module Who2.Expr.Filter
  ( Filter
  , getFilter
  , empty
  , disabled
  , insert
  , mightContain
  , disjoint
  , union
  ) where

import Data.Bits (testBit, setBit, complement, (.&.), (.|.))
import Data.Hashable (Hashable(hash))
import Data.Word (Word64)

import Who2.Config (bloomFilter)

------------------------------------------------------------------------
-- Type and instances
------------------------------------------------------------------------

-- | A 64-bit bloom filter for fast negative membership tests
newtype Filter a = Filter { getFilter :: Word64 }
  deriving (Eq, Ord, Show)

------------------------------------------------------------------------
-- Operations
------------------------------------------------------------------------

-- | Disabled filter (all 1 bits) - used when filter is turned off
disabled :: Filter a
disabled = Filter (complement 0)
{-# INLINE disabled #-}

-- | Empty filter (all 0 bits if enabled, disabled if not)
empty :: Filter a
empty = if bloomFilter then Filter 0 else disabled
{-# INLINE empty #-}

-- | Insert an element into the filter
insert :: Hashable a => Filter a -> a -> Filter a
insert f@(Filter w) x
  | f == disabled = disabled
  | otherwise = Filter (setBit w (hash x .&. 63))
{-# INLINE insert #-}

-- | Check if element might be in the filter
mightContain :: Hashable a => Filter a -> a -> Bool
mightContain f@(Filter w) x
  | f == disabled = True
  | otherwise = testBit w (hash x .&. 63)
{-# INLINE mightContain #-}

disjoint :: Filter a -> Filter a -> Bool
disjoint (Filter x) (Filter y) = x .&. y == 0
{-# INLINE disjoint #-}

union :: Filter a -> Filter a -> Filter a
union (Filter x) (Filter y) = Filter (x .|. y)
{-# INLINE union #-}

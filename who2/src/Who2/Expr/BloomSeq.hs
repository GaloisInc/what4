{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StrictData #-}

-- | A fast set-like data-structure.
--
-- This is a normalizing datastructure for associative, idempotent operations,
-- see "What4.Expr.App" for an overview of such data structures.
module Who2.Expr.BloomSeq
  ( BloomSeq(..)
  , empty
  , singleton
  , fromTwo
  , fromList
  , size
  , isEmpty
  , toSeq
  , toList
  , containsFast
  , containsAnyFast
  , insert
  , insertIfNotPresent
  , merge
  , eqBy
  , ordBy

  , -- * Configuration
    threshold
  ) where

import Data.Hashable (Hashable(hashWithSalt))
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Foldable as F
import qualified Who2.Expr.Filter as Filt
import Who2.Expr.Filter (Filter)
import qualified Who2.Expr.HashedSequence as HS

---------------------------------------------------------------------

-- | A fast set-like data-structure.
--
-- Under a certain size 'threshold', 'insertIfNotPresent' will avoid inserting
-- duplicate elements using a simple bloom filter. Above the threshold, it acts
-- like a simple list, appending elements in constant time.
--
-- The 'Filter' holds the hashes of the elements in the sequence in the bits
-- of a 64-bit word. If bit @i@ of the 'Filter' is 1, there is an element
-- with that hash in the sequence. This enables @O(1)@ negative lookups: if an
-- element's hash is not in the filter, the element is certainly not present in
-- the sequence.
--
-- The hash values are computed as @(.&. 63) . 'hash'@. This clamps the has
-- values to the range @[0..64)@ while preserving their distribution. This is
-- roughly equivalent to @'hash' x `mod` 64@, but is faster because it's only a
-- single bitwise operation.
--
-- When the sequence reaches the threshold, the filter is set to all 1s
-- (disabled) and inserts become unconditional (no duplicate checking) to avoid
-- the performance penalty of linear search through large sequences.
data BloomSeq a = BloomSeq
  { filt :: {-# UNPACK #-} !(Filter a)
  , elems :: !(HS.HashedSeq a)
  }
  deriving (Eq, Ord, Show)

instance Foldable BloomSeq where
  foldMap f = foldMap f . elems
  {-# INLINE foldMap #-}

-- | Hash instance - delegates to HashedSeq for O(1) hashing
instance Hashable a => Hashable (BloomSeq a) where
  hashWithSalt salt bs = hashWithSalt salt (elems bs)

-- | Threshold for disabling filter.
--
-- Due to the birthday paradox, this gives a 2/3 chance of one collision.
threshold :: Int
threshold = 12
{-# INLINE threshold #-}

-- | Empty sequence
empty :: BloomSeq a
empty = BloomSeq Filt.empty HS.empty
{-# INLINE empty #-}

-- | Create single-element sequence
singleton :: (Eq a, Hashable a) => a -> BloomSeq a
singleton x = BloomSeq (Filt.insert Filt.empty x) (HS.singleton x)

-- | Create from 2 elements (handles x==y case)
fromTwo :: (Eq a, Hashable a) => a -> a -> BloomSeq a
fromTwo x y  -- TODO: Assert x /= y
  | x == y = singleton x
  | otherwise =
      let f = Filt.insert (Filt.insert Filt.empty x) y
      in BloomSeq f (HS.fromList [x, y])

-- | Create from list
fromList :: (Eq a, Hashable a) => [a] -> BloomSeq a
fromList = F.foldl' insertIfNotPresent empty
{-# INLINE fromList #-}

-- | Return size of sequence
size :: BloomSeq a -> Int
size = HS.length . elems
{-# INLINE size #-}

-- | Check if sequence is empty
isEmpty :: BloomSeq a -> Bool
isEmpty = HS.null . elems
{-# INLINE isEmpty #-}

-- | Get the underlying sequence
toSeq :: BloomSeq a -> Seq a
toSeq = HS.toSeq . elems
{-# INLINE toSeq #-}

-- | Convert to list
toList :: BloomSeq a -> [a]
toList = F.toList . elems
{-# INLINE toList #-}

-- | Check membership using filter then linear search if needed
_contains :: (Eq a, Hashable a) => BloomSeq a -> a -> Bool
_contains (BloomSeq f es) x
  | not Filt.enabled = x `elem` es
  | not (Filt.mightContain f x) = False
  | otherwise = x `elem` es
{-# INLINE _contains #-}

-- | Check membership using filter but only search if under threshold
containsFast :: (Eq a, Hashable a) => BloomSeq a -> a -> Bool
containsFast (BloomSeq f es) x
  | not Filt.enabled = False
  | f == Filt.disabled = False
  | Filt.mightContain f x = x `elem` es
  | otherwise = False
{-# INLINE containsFast #-}

-- | Check membership using filter but only search if under threshold
containsAnyFast :: (Eq a, Hashable a, Foldable t) => BloomSeq a -> t a -> Bool
containsAnyFast (BloomSeq f es) xs
  | not Filt.enabled = False
  | f == Filt.disabled = False
  | otherwise =
    any (\x -> if Filt.mightContain f x then x `elem` es else False) xs
{-# INLINE containsAnyFast #-}

-- | Insert element unconditionally (appends to end, updates filter)
insert :: (Eq a, Hashable a) => BloomSeq a -> a -> BloomSeq a
insert (BloomSeq f es) x =
  let newSize = HS.length es + 1
      newFilter = if not Filt.enabled || newSize > threshold
                  then Filt.disabled
                  else Filt.insert f x
      newElems = es HS.|> x
  in BloomSeq newFilter newElems
{-# INLINE insert #-}

-- | Insert only if not already present (unless filter is disabled)
insertIfNotPresent :: (Eq a, Hashable a) => BloomSeq a -> a -> BloomSeq a
insertIfNotPresent bs@(BloomSeq f _) x
  | not Filt.enabled = insert bs x
  | f == Filt.disabled = insert bs x
  | containsFast bs x = bs
  | otherwise = insert bs x
{-# INLINE insertIfNotPresent #-}

-- | Merge two sequences
merge :: (Eq a, Hashable a) => BloomSeq a -> BloomSeq a -> BloomSeq a
merge xs ys
  | not Filt.enabled = merged
  | filt xs == Filt.disabled || filt ys == Filt.disabled = merged
  | Filt.disjoint (filt xs) (filt ys) =
      BloomSeq (Filt.union (filt xs) (filt ys)) (elems xs HS.>< elems ys)
  | otherwise = F.foldl' insertIfNotPresent xs (elems ys)
  where merged = BloomSeq Filt.disabled (elems xs HS.>< elems ys)
{-# INLINE merge #-}

eqBy :: (a -> a -> Bool) -> BloomSeq a -> BloomSeq a -> Bool
eqBy cmp x y =
  if filt x /= filt y
  then False
  else and (Seq.zipWith cmp (HS.toSeq (elems x)) (HS.toSeq (elems y)))

ordBy :: (a -> a -> Ordering) -> BloomSeq a -> BloomSeq a -> Ordering
ordBy cmp x y =
  case compare (filt x) (filt y) of
    LT -> LT
    GT -> GT
    EQ -> HS.ordBy cmp (elems x) (elems y)

{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StrictData #-}

-- | A bloom-filtered key-value map optimized for small sizes
--
-- This data structure uses a bloom filter for O(1) negative lookups, similar to
-- 'BloomSeq'. Below a certain threshold, it maintains single-value-per-key
-- semantics (last-wins). Above the threshold, it transitions to multimap mode
-- where insertions are unconditional appends without searching for duplicates.
module Who2.Expr.BloomKv
  ( BloomKv(..)
  , Kv(..)
  , empty
  , singleton
  , fromList
  , size
  , isEmpty
  , toList
  , keys
  , values
  , insert
  , merge
  , eqBy
  , ordBy

  , -- * Configuration
    threshold
  ) where

import qualified Prelude as P
import Prelude (Eq, Ord, Show, Bool, Int, Ordering, Functor, Foldable, (==), (/=), (>), (&&), (||), (+), (.))
import Data.Hashable (Hashable(hashWithSalt))
import qualified Data.Sequence as Seq
import qualified Data.Foldable as F
import qualified Who2.Expr.Filter as Filt
import Who2.Expr.Filter (Filter)
import qualified Who2.Expr.HashedSequence as HS

---------------------------------------------------------------------

-- | Key-value pair (internal representation)
data Kv k v = Kv
  { kvKey :: !k
  , kvValue :: !v
  }
  deriving (Eq, Ord, Show, Functor)

-- | Hashable instance for Kv
instance (Hashable k, Hashable v) => Hashable (Kv k v) where
  hashWithSalt s (Kv k v) = s `hashWithSalt` k `hashWithSalt` v

---------------------------------------------------------------------

-- | A bloom-filtered key-value map optimized for small sizes
--
-- Below 'threshold', maintains single-value-per-key semantics with O(1) negative
-- lookups via bloom filter. Above threshold, transitions to multimap mode where
-- inserts become unconditional appends (avoiding expensive linear searches).
data BloomKv k v = BloomKv
  { filt :: {-# UNPACK #-} !(Filter k)
  , kvs :: !(HS.HashedSeq (Kv k v))
  }
  deriving (Eq, Ord, Show)

instance Foldable (BloomKv k) where
  foldMap f = P.foldMap (f . kvValue) . kvs
  {-# INLINE foldMap #-}

-- | Threshold for disabling filter
--
-- Due to the birthday paradox, this gives a 2/3 chance of one collision.
threshold :: Int
threshold = 12
{-# INLINE threshold #-}

-- | Empty map
empty :: BloomKv k v
empty = BloomKv Filt.empty HS.empty
{-# INLINE empty #-}

-- | Create single-element map
singleton :: (Eq k, Hashable k, Hashable v) => k -> v -> BloomKv k v
singleton k v = BloomKv (Filt.insert Filt.empty k) (HS.singleton (Kv k v))

-- | Create from list of key-value pairs
fromList :: (Eq k, Hashable k, Hashable v) => (v -> v -> v) -> [(k, v)] -> BloomKv k v
fromList combine = F.foldl' (\acc (k, v) -> insert combine acc k v) empty
{-# INLINE fromList #-}

-- | Return size of map (total number of pairs, may include duplicates)
size :: BloomKv k v -> Int
size = HS.length . kvs
{-# INLINE size #-}

-- | Check if map is empty
isEmpty :: BloomKv k v -> Bool
isEmpty = HS.null . kvs
{-# INLINE isEmpty #-}

-- | Convert to list
toList :: BloomKv k v -> [(k, v)]
toList = P.map (\(Kv k v) -> (k, v)) . HS.toList . kvs
{-# INLINE toList #-}

-- | Extract all keys
keys :: BloomKv k v -> [k]
keys = P.map kvKey . HS.toList . kvs
{-# INLINE keys #-}

-- | Extract all values
values :: BloomKv k v -> [v]
values = P.map kvValue . HS.toList . kvs
{-# INLINE values #-}

-- | Insert key-value pair with combine function
--
-- Below threshold: Searches for existing key and combines values (last-wins if no combine).
-- Above threshold: Unconditionally appends without searching (multimap mode).
insert ::
  (Eq k, Hashable k, Hashable v) =>
  (v -> v -> v) ->
  BloomKv k v ->
  k ->
  v ->
  BloomKv k v
insert combine (BloomKv f kvSeq) key newVal
  | P.not Filt.enabled = appendNew Filt.disabled kvSeq
  | f == Filt.disabled = appendNew Filt.disabled kvSeq
  | P.not (Filt.mightContain f key) = appendNew newFilter kvSeq
  | P.otherwise =
      case HS.findIndexR (\(Kv k _) -> k == key) kvSeq of
        P.Just idx ->
          let upd (Kv k oldV) = Kv k (combine oldV newVal) in
          BloomKv f (HS.adjust' upd idx kvSeq)
        P.Nothing ->
          appendNew newFilter kvSeq
  where
    newFilter =
      let newSize = HS.length kvSeq + 1
      in if P.not Filt.enabled || newSize > threshold
         then Filt.disabled
         else Filt.insert f key

    appendNew flt sq = BloomKv flt (sq HS.|> Kv key newVal)
{-# INLINE insert #-}

-- | Merge two maps with combine function
merge :: (Eq k, Ord k, Hashable k, Hashable v) => (v -> v -> v) -> BloomKv k v -> BloomKv k v -> BloomKv k v
merge combine xs ys
  | P.not Filt.enabled = merged
  | filt xs == Filt.disabled || filt ys == Filt.disabled = merged
  | Filt.disjoint (filt xs) (filt ys) =
      BloomKv (Filt.union (filt xs) (filt ys)) (kvs xs HS.>< kvs ys)
  | P.otherwise = F.foldl' (\acc (Kv k v) -> insert combine acc k v) xs (kvs ys)
  where merged = BloomKv Filt.disabled (kvs xs HS.>< kvs ys)
{-# INLINE merge #-}

-- | Equality with custom comparisons
eqBy :: (k -> k -> Bool) -> (v -> v -> Bool) -> BloomKv k v -> BloomKv k v -> Bool
eqBy cmpK cmpV x y =
  if filt x /= filt y
  then P.False
  else F.and (Seq.zipWith (\(Kv k1 v1) (Kv k2 v2) -> cmpK k1 k2 && cmpV v1 v2) (HS.toSeq (kvs x)) (HS.toSeq (kvs y)))

-- | Ordering with custom comparisons
ordBy :: (k -> k -> Ordering) -> (v -> v -> Ordering) -> BloomKv k v -> BloomKv k v -> Ordering
ordBy cmpK cmpV x y =
  case P.compare (filt x) (filt y) of
    P.LT -> P.LT
    P.GT -> P.GT
    P.EQ -> HS.ordBy cmpKv (kvs x) (kvs y)
  where
    cmpKv (Kv k1 v1) (Kv k2 v2) =
      case cmpK k1 k2 of
        P.LT -> P.LT
        P.GT -> P.GT
        P.EQ -> cmpV v1 v2

-- | Hash instance - delegates to HashedSeq for O(1) hashing
instance (Hashable k, Hashable v) => Hashable (BloomKv k v) where
  hashWithSalt salt bkv = hashWithSalt salt (kvs bkv)

{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StrictData #-}

-- | A bloom-filtered key-value map optimized for small sizes
--
-- This data structure uses a bloom filter for O(1) negative lookups, similar to
-- 'BloomSeq'. Below a certain threshold, it maintains single-value-per-key
-- semantics (last-wins). Above the threshold, it transitions to multimap mode
-- where insertions are unconditional appends without searching for duplicates.
module Who2.Expr.Bloom.Map
  ( BloomKv(..)
  , eqBy2
  , ordBy2
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

  , -- * Configuration
    threshold
  ) where

import Data.Functor.Classes (Eq1(liftEq), Ord1(liftCompare), Eq2(liftEq2), Ord2(liftCompare2))
import Data.Hashable (Hashable(hashWithSalt))
import qualified Data.Foldable as F
import qualified Who2.Expr.Bloom.Filter as Filt
import Who2.Expr.Bloom.Filter (Filter)
import qualified Who2.Expr.Bloom.HashedSeq as HS

import Who2.Config (bloomFilter)

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

eqBy2Kv ::
  (k1 -> k2 -> Bool) ->
  (v1 -> v2 -> Bool) ->
  Kv k1 v1 ->
  Kv k2 v2 ->
  Bool
eqBy2Kv eqK eqV (Kv k1 v1) (Kv k2 v2) = eqK k1 k2 && eqV v1 v2
{-# INLINE eqBy2Kv #-}

ordBy2Kv ::
  (k1 -> k2 -> Ordering) ->
  (v1 -> v2 -> Ordering) ->
  Kv k1 v1 ->
  Kv k2 v2 ->
  Ordering
ordBy2Kv cmpK cmpV (Kv k1 v1) (Kv k2 v2) =
  case cmpK k1 k2 of
    LT -> LT
    GT -> GT
    EQ -> cmpV v1 v2
{-# INLINE ordBy2Kv #-}

------------------------------------------------------------------------
-- Type and instances
------------------------------------------------------------------------

-- | A bloom-filtered key-value map optimized for small sizes
--
-- Below 'threshold', maintains single-value-per-key semantics with O(1) negative
-- lookups via bloom filter. Above threshold, transitions to multimap mode where
-- inserts become unconditional appends (avoiding expensive linear searches).
data BloomKv k v = BloomKv
  { filt :: {-# UNPACK #-} !(Filter k)
  , kvs :: !(HS.HashedSeq (Kv k v))
  }
  deriving Show

instance Foldable (BloomKv k) where
  foldMap f = foldMap (f . kvValue) . kvs
  {-# INLINE foldMap #-}

-- | Like 'liftCompare2', but without typeclass constraints
eqBy2 ::
  (k1 -> k2 -> Bool) ->
  (v1 -> v2 -> Bool) ->
  BloomKv k1 v1 ->
  BloomKv k2 v2 ->
  Bool
eqBy2 eqK eqV x y =
  let fx = filt x in
  let fy = filt y in
  if bloomFilter && (Filt.getFilter fx /= Filt.getFilter fy)
  then False
  else HS.eqBy (eqBy2Kv eqK eqV) (kvs x) (kvs y)
{-# INLINE eqBy2 #-}

-- test-law: propBloomKvEqByReflexive
-- test-law: propBloomKvEqBySymmetric
-- test-law: propBloomKvEqByTransitive
-- | @'eqBy2' (==) (==)@
instance (Eq k, Eq v) => Eq (BloomKv k v) where
  (==) = eqBy2 (==) (==)
  {-# INLINE (==) #-}

-- | @'eqBy2' (==)@
instance Eq k => Eq1 (BloomKv k) where
  liftEq = eqBy2 (==)
  {-# INLINE liftEq #-}

-- | @'eqBy2'@
instance Eq2 BloomKv where
  liftEq2 = eqBy2
  {-# INLINE liftEq2 #-}

-- | Like 'liftCompare2', but without typeclass constraints
ordBy2 ::
  (k1 -> k2 -> Ordering) ->
  (v1 -> v2 -> Ordering) ->
  BloomKv k1 v1 ->
  BloomKv k2 v2 ->
  Ordering
ordBy2 cmpK cmpV x y =
  let fx = filt x in
  let fy = filt y in
  if bloomFilter
  then
    case compare (Filt.getFilter fx) (Filt.getFilter fy) of
      EQ -> HS.ordBy (ordBy2Kv cmpK cmpV) (kvs x) (kvs y)
      r -> r
  else HS.ordBy (ordBy2Kv cmpK cmpV) (kvs x) (kvs y)
{-# INLINE ordBy2 #-}

-- test-law: propBloomKvOrdByReflexive
-- test-law: propBloomKvOrdByAntisymmetric
-- test-law: propBloomKvOrdByTransitive
-- test-law: propBloomKvOrdByConsistentWithEqBy
-- | @'ordBy2' 'compare' 'compare'@
instance (Ord k, Ord v) => Ord (BloomKv k v) where
  compare = ordBy2 compare compare
  {-# INLINE compare #-}

-- | @'ordBy2' 'compare'@
instance Ord k => Ord1 (BloomKv k) where
  liftCompare = ordBy2 compare
  {-# INLINE liftCompare #-}

-- | @'ordBy2'@
instance Ord2 BloomKv where
  liftCompare2 = ordBy2
  {-# INLINE liftCompare2 #-}

-- | Hash instance - delegates to HashedSeq for O(1) hashing
--
-- No dedicated property tests - hash correctness is validated through Eq consistency.
instance (Hashable k, Hashable v) => Hashable (BloomKv k v) where
  hashWithSalt salt bkv = hashWithSalt salt (kvs bkv)

------------------------------------------------------------------------
-- Operations
------------------------------------------------------------------------

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
fromList :: (Eq k, Hashable k, Hashable v) => (v -> v -> Maybe v) -> [(k, v)] -> BloomKv k v
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
toList = map (\(Kv k v) -> (k, v)) . HS.toList . kvs
{-# INLINE toList #-}

-- | Extract all keys
keys :: BloomKv k v -> [k]
keys = map kvKey . HS.toList . kvs
{-# INLINE keys #-}

-- | Extract all values
values :: BloomKv k v -> [v]
values = map kvValue . HS.toList . kvs
{-# INLINE values #-}

-- | Insert key-value pair with combine function
--
-- Below threshold: Searches for existing key and combines values (last-wins if no combine).
-- Above threshold: Unconditionally appends without searching (multimap mode).
insert ::
  (Eq k, Hashable k, Hashable v) =>
  (v -> v -> Maybe v) ->
  BloomKv k v ->
  k ->
  v ->
  BloomKv k v
insert combine (BloomKv f kvSeq) key newVal
  | not bloomFilter = appendNew Filt.disabled kvSeq
  | f == Filt.disabled = appendNew Filt.disabled kvSeq
  | not (Filt.mightContain f key) = appendNew newFilter kvSeq
  | otherwise =
      case HS.findIndexR (\(Kv k _) -> k == key) kvSeq of
        Just idx ->
          case combine (kvValue (HS.index kvSeq idx)) newVal of
            Just v' ->
              let upd (Kv k _) = Kv k v' in
              BloomKv f (HS.adjust' upd idx kvSeq)
            Nothing ->
              -- Bloom filters don't support deletion, so disable the filter
              BloomKv Filt.disabled (HS.deleteAt idx kvSeq)
        Nothing ->
          appendNew newFilter kvSeq
  where
    newFilter =
      let newSize = HS.length kvSeq + 1
      in if not bloomFilter || newSize > threshold
         then Filt.disabled
         else Filt.insert f key

    appendNew flt sq = BloomKv flt (sq HS.|> Kv key newVal)
{-# INLINE insert #-}

-- | Merge two maps with combine function
merge :: (Eq k, Ord k, Hashable k, Hashable v) => (v -> v -> Maybe v) -> BloomKv k v -> BloomKv k v -> BloomKv k v
merge combine xs ys
  | not bloomFilter = merged
  | filt xs == Filt.disabled || filt ys == Filt.disabled = merged
  | Filt.disjoint (filt xs) (filt ys) =
      BloomKv (Filt.union (filt xs) (filt ys)) (kvs xs HS.>< kvs ys)
  | otherwise =
      let result = F.foldl' (\acc (Kv k v) -> insert combine acc k v) xs (kvs ys)
      in if isEmpty result then empty else result
  where merged = BloomKv Filt.disabled (kvs xs HS.>< kvs ys)
{-# INLINE merge #-}

{-# LANGUAGE StrictData #-}

module Who2.Expr.Bloom.HashedSeq
  ( HashedSeq
  , eqBy
  , ordBy
  , empty
  , singleton
  , fromList
  , fromSeq
  , Who2.Expr.Bloom.HashedSeq.length
  , Who2.Expr.Bloom.HashedSeq.null
  , (|>)
  , (><)
  , toSeq
  , toList
  , findIndexR
  , adjust'
  , deleteAt
  , index
  ) where

import Data.Bits (xor, shiftR, (.&.))
import qualified Data.Foldable as F
import Data.Functor.Classes (Eq1(liftEq), Ord1(liftCompare))
import Data.Hashable (Hashable(hash, hashWithSalt))
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import Who2.Config (hashedSequence, fancyHash)

------------------------------------------------------------------------
-- Type and instances
------------------------------------------------------------------------

-- | Sequence with optional precomputed hash (controlled by 'hashedSequence').
--
-- Hash computation strategy (controlled by 'fancyHash', only when hashedSequence = True):
-- - When fancyHash = True (polynomial rolling hash with base 31):
--   * append x: new_hash = old_hash * 31 + hash x (with natural Int overflow)
--   * merge:    new_hash = hash1 * 31^len2 + hash2 (with natural Int overflow)
-- - When fancyHash = False (simple XOR):
--   * append x: new_hash = old_hash `xor` hash x
--   * merge:    new_hash = hash1 `xor` hash2
data HashedSeq a = HashedSeq
  { hsSeq :: !(Seq a)
    -- | INVARIANT: If 'hashedSequence' is 'True', this is the hash of the
    -- elements in 'hsSeq'. Otherwise, it is 0.
  , hsHash :: {-# UNPACK #-} !Int
  }
  -- DO NOT derive or implement Functor nor Traversable, as they would break
  -- the invariant.
  deriving (Show)

-- | Like 'liftEq', but without typeclass constraints
eqBy ::
  (a -> b -> Bool) ->
  HashedSeq a ->
  HashedSeq b ->
  Bool
eqBy eq (HashedSeq s1 h1) (HashedSeq s2 h2) =
  if hashedSequence && h1 /= h2
  then False
  else liftEq eq s1 s2
{-# INLINE eqBy #-}

-- test-law: propHashedSeqEqConsistency
-- | @'eqBy' (==)@
instance Eq a => Eq (HashedSeq a) where
  (==) = eqBy (==)
  {-# INLINE (==) #-}

-- | @eqBy@
instance Eq1 HashedSeq where
  liftEq = eqBy
  {-# INLINE liftEq #-}

-- | Like 'liftCompare', but without typeclass constraints
ordBy ::
  (a -> b -> Ordering) ->
  HashedSeq a ->
  HashedSeq b ->
  Ordering
ordBy cmp (HashedSeq s1 h1) (HashedSeq s2 h2) =
  if hashedSequence
  then
    case compare h1 h2 of
      EQ -> liftCompare cmp s1 s2
      r -> r
  else liftCompare cmp s1 s2
{-# INLINE ordBy #-}

-- test-law: propHashedSeqOrdByReflexive
-- test-law: propHashedSeqOrdByAntisymmetric
-- test-law: propHashedSeqOrdByTransitive
-- | @'ordBy' 'compare'@
instance Ord a => Ord (HashedSeq a) where
  compare = ordBy compare
  {-# INLINE compare #-}

-- | @'ordBy'@
instance Ord1 HashedSeq where
  liftCompare = ordBy
  {-# INLINE liftCompare #-}

-- test-law: propHashedSeqHashConsistency
-- test-law: propHashedSeqAppendHashConsistency
-- test-law: propHashedSeqMergeHashConsistency
instance Hashable a => Hashable (HashedSeq a) where
  hash hs = if hashedSequence then hsHash hs else hash (hsSeq hs)
  {-# INLINE hash #-}

  hashWithSalt salt hs =
    if hashedSequence then salt `xor` hsHash hs else hashWithSalt salt (hsSeq hs)
  {-# INLINE hashWithSalt #-}

-- | Delegates to underlying 'Seq'
instance F.Foldable HashedSeq where
  foldMap f = F.foldMap f . hsSeq
  {-# INLINE foldMap #-}
  foldr f z = F.foldr f z . hsSeq
  {-# INLINE foldr #-}
  foldl' f z = F.foldl' f z . hsSeq
  {-# INLINE foldl' #-}
  length = Seq.length . hsSeq
  {-# INLINE length #-}
  null = Seq.null . hsSeq
  {-# INLINE null #-}

------------------------------------------------------------------------
-- Operations
------------------------------------------------------------------------

-- | O(1). The empty sequence with hash 0.
empty :: HashedSeq a
empty = HashedSeq Seq.empty 0
{-# INLINE empty #-}

-- | O(1). A singleton sequence with precomputed hash (if hashedSequence).
singleton :: Hashable a => a -> HashedSeq a
singleton x = HashedSeq (Seq.singleton x) (if hashedSequence then hash x else 0)
{-# INLINE singleton #-}

-- | O(n). Build a hashed sequence from a list.
fromList :: Hashable a => [a] -> HashedSeq a
fromList = F.foldl' (|>) empty

-- | O(n). Build a hashed sequence from a Seq, computing the hash (if hashedSequence).
fromSeq :: Hashable a => Seq a -> HashedSeq a
fromSeq s =
  if hashedSequence
  then HashedSeq s (F.foldl' (\h x -> combineHashAppend h (hash x)) 0 s)
  else HashedSeq s 0

-- | O(1). The number of elements in the sequence.
length :: HashedSeq a -> Int
length = Seq.length . hsSeq
{-# INLINE length #-}

-- | O(1). Is the sequence empty?
null :: HashedSeq a -> Bool
null = Seq.null . hsSeq
{-# INLINE null #-}

-- | O(1). Add an element to the right end of the sequence.
-- The hash is updated incrementally (if hashedSequence).
(|>) :: Hashable a => HashedSeq a -> a -> HashedSeq a
(|>) (HashedSeq s h) x =
  if hashedSequence
  then HashedSeq (s Seq.|> x) (combineHashAppend h (hash x))
  else HashedSeq (s Seq.|> x) 0

infixl 5 |>

-- | O(log(min(n1,n2))). Concatenate two sequences.
-- The hash is combined incrementally (if hashedSequence).
(><) :: HashedSeq a -> HashedSeq a -> HashedSeq a
(><) (HashedSeq s1 h1) (HashedSeq s2 h2) =
  if hashedSequence
  then HashedSeq (s1 Seq.>< s2) (combineHashConcat h1 h2 (Seq.length s2))
  else HashedSeq (s1 Seq.>< s2) 0

infixr 5 ><

-- | O(1). Extract the underlying sequence.
toSeq :: HashedSeq a -> Seq a
toSeq = hsSeq
{-# INLINE toSeq #-}

-- | O(n). Convert to a list.
toList :: HashedSeq a -> [a]
toList = F.toList . hsSeq
{-# INLINE toList #-}

-- | O(n). Find the rightmost index matching a predicate.
findIndexR :: (a -> Bool) -> HashedSeq a -> Maybe Int
findIndexR p = Seq.findIndexR p . hsSeq
{-# INLINE findIndexR #-}

-- | O(n). Update the element at the given index.
-- The hash is recomputed (if hashedSequence) because we can't incrementally update
-- when modifying an interior element.
adjust' :: Hashable a => (a -> a) -> Int -> HashedSeq a -> HashedSeq a
adjust' f i hs@(HashedSeq s _) =
  let newSeq = Seq.adjust' f i s
  in if s == newSeq  -- TODO: Just compare the one element
     then hs  -- No change
     else mkHashedSeq newSeq

-- | O(log(min(i,n-i))). Delete the element at the given index.
-- The hash is recomputed (if hashedSequence) because we can't incrementally update
-- when deleting an interior element.
deleteAt :: Hashable a => Int -> HashedSeq a -> HashedSeq a
deleteAt i (HashedSeq s _) = mkHashedSeq (Seq.deleteAt i s)

-- | Create a HashedSeq from a Seq, computing the hash if needed
mkHashedSeq :: Hashable a => Seq a -> HashedSeq a
mkHashedSeq s
  | hashedSequence = HashedSeq s (F.foldl' (\h x -> combineHashAppend h (hash x)) 0 s)
  | otherwise = HashedSeq s 0

-- | O(log(min(i,n-i))). Get the element at the given index.
index :: HashedSeq a -> Int -> a
index (HashedSeq s _) i = Seq.index s i

------------------------------------------------------------------------
-- Hash helpers
------------------------------------------------------------------------

-- | Base for polynomial rolling hash (only used when fancyHash = True)
hashBase :: Int
hashBase = 31
{-# INLINE hashBase #-}

-- | Fast integer exponentiation: base^exp
-- Uses natural Int overflow (2^64 modulus) for consistency
pow :: Int -> Int -> Int
pow base ex
  | ex < 0 = error "pow: negative eonent"
  | ex == 0 = 1
  | otherwise = go base ex 1
  where
    go _ 0 acc = acc
    go b e acc
      | e .&. 1 == 1 = go b' e' (acc * b)
      | otherwise      = go b' e' acc
      where
        b' = b * b
        e' = e `shiftR` 1
{-# INLINE pow #-}

-- | Combine hash when appending single element
combineHashAppend :: Int -> Int -> Int
combineHashAppend oldHash elemHash =
  if fancyHash
  then oldHash * hashBase + elemHash
  else oldHash `xor` elemHash
{-# INLINE combineHashAppend #-}

-- | Combine hash when concatenating sequences
-- Takes: hash1, hash2, length2
combineHashConcat :: Int -> Int -> Int -> Int
combineHashConcat hash1 hash2 len2 =
  if fancyHash
  then hash1 * pow hashBase len2 + hash2
  else hash1 `xor` hash2
{-# INLINE combineHashConcat #-}

{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}

-- | Sequences that track elements by polarity (positive and negative/complemented)
--
-- This is a normalizing datastructure for associative, idempotent operations
-- with complementation, see "What4.Expr.App" for an overview of such data
-- structures.
--
-- A 'PolarizedBloomSeq' stores two 'BloomSeq's: one for positive polarity
-- elements and one for negative/complemented elements. For relatively small
-- sequences, this enables efficient complement detection for operations like:
--
-- * @x && (not x)@ => @false@
-- * @x || (not x)@ => @true@
-- * @x & (~x)@ => @0@
-- * @x | (~x)@ => @~0@
module Who2.Expr.Bloom.Polarized
  ( PolarizedBloomSeq(..)
  , Polarized(..)
  , Polarizable(..)
  , Simplified(..)
  , eqBy
  , ordBy
  , insertIfNotPresent
  , fromTwo
  , merge
  , sizePos
  , sizeNeg
  , totalSize
  , toListPos
  , toListNeg
  , allElems
  , simplify
  , isEmpty
  , hashPBSWith
  , hashPBS
  , hashPBSF
  ) where

import Data.Functor.Classes (Eq1(liftEq), Ord1(liftCompare))
import Data.Hashable (Hashable(hashWithSalt))
import Data.Kind (Type)
import qualified Data.Parameterized.Classes as PC
import qualified Who2.Expr.Bloom.Seq as BS

------------------------------------------------------------------------
-- Class
------------------------------------------------------------------------

-- | A value tagged with its polarity
data Polarized a = Positive a | Negative a
  deriving (Eq, Ord, Show, Foldable)

-- | Typeclass for types that can determine their polarity
class Polarizable a where
  -- | Extract the polarity of a value
  -- For expressions: NotPred/BVNotBits return Negative inner, others return Positive self
  polarity :: a -> Polarized a

------------------------------------------------------------------------
-- Type and instances
------------------------------------------------------------------------

-- | A sequence split by polarity
data PolarizedBloomSeq a = PolarizedBloomSeq
  { positive :: !(BS.BloomSeq a)  -- ^ Positive polarity elements
  , negative :: !(BS.BloomSeq a)  -- ^ Negative polarity elements
  }
  deriving (Show, Foldable)

-- | Like 'liftEq', but without typeclass constraints
eqBy ::
  (a1 -> a2 -> Bool) ->
  PolarizedBloomSeq a1 ->
  PolarizedBloomSeq a2 ->
  Bool
eqBy cmp x y =
  BS.eqBy cmp (positive x) (positive y) && BS.eqBy cmp (negative x) (negative y)
{-# INLINE eqBy #-}

-- | @'eqBy' (==)@
instance Eq a => Eq (PolarizedBloomSeq a) where
  (==) = eqBy (==)
  {-# INLINE (==) #-}

-- | @'eqBy'@
instance Eq1 PolarizedBloomSeq where
  liftEq = eqBy
  {-# INLINE liftEq #-}

-- | Like 'liftCompare', but without typeclass constraints
ordBy ::
  (a1 -> a2 -> Ordering) ->
  PolarizedBloomSeq a1 ->
  PolarizedBloomSeq a2 ->
  Ordering
ordBy cmp x y =
  case BS.ordBy cmp (positive x) (positive y) of
    LT -> LT
    GT -> GT
    EQ -> BS.ordBy cmp (negative x) (negative y)
{-# INLINE ordBy #-}

-- | @'ordBy' 'compare'@
instance Ord a => Ord (PolarizedBloomSeq a) where
  compare = ordBy compare
  {-# INLINE compare #-}

-- | @'ordBy'@
instance Ord1 PolarizedBloomSeq where
  liftCompare = ordBy
  {-# INLINE liftCompare #-}

instance Hashable a => Hashable (PolarizedBloomSeq a) where
  hashWithSalt salt pbs =
    let salt' = hashWithSalt salt (positive pbs)
    in hashWithSalt salt' (negative pbs)

------------------------------------------------------------------------
-- Operations
------------------------------------------------------------------------

data Simplified a
  = -- | An item and its complement were found
    Inconsistent
    -- | Just one item was found, and it was positive
  | SinglePositive a
    -- | Just one item was found, and it was negative
  | SingleNegative a
  | Merged (PolarizedBloomSeq a)

-- | Returns Just x if only one positive element exists, Nothing otherwise
simplify :: PolarizedBloomSeq a -> Simplified a
simplify pbs =
  case (BS.toList (positive pbs), BS.toList (negative pbs)) of
    ([], []) -> Inconsistent
    ([x], []) -> SinglePositive x
    ([], [x]) -> SingleNegative x
    _ -> Merged pbs

-- | Empty polarized sequence (both sequences empty)
empty :: PolarizedBloomSeq a
empty = PolarizedBloomSeq BS.empty BS.empty
{-# INLINE empty #-}

-- | Insert only if not already present, c.f. 'BS.insertIfNotPresent'
insertIfNotPresent :: (Eq w, Hashable w, Polarizable w) => PolarizedBloomSeq w -> w -> Maybe (PolarizedBloomSeq w)
insertIfNotPresent pbs wx =
  case polarity wx of
    Positive inner ->
      if BS.containsFast (negative pbs) inner
      then Nothing
      else Just (pbs { positive = BS.insertIfNotPresent (positive pbs) inner })
    Negative inner ->
      if BS.containsFast (positive pbs) inner
      then Nothing
      else Just (pbs { negative = BS.insertIfNotPresent (negative pbs) inner })
{-# INLINE insertIfNotPresent #-}

-- | Create from two elements, c.f., 'BS.fromTwo'
fromTwo :: (Eq w, Hashable w, Polarizable w) => w -> w -> Simplified w
fromTwo wx wy =
  case flip insertIfNotPresent wy =<< insertIfNotPresent empty wx of
    Nothing -> Inconsistent
    Just pbs -> simplify pbs
{-# INLINE fromTwo #-}

-- | Merge two polarized sequences
merge ::
  (Eq a, Hashable a) =>
  PolarizedBloomSeq a ->
  PolarizedBloomSeq a ->
  Maybe (PolarizedBloomSeq a)
merge pbs1 pbs2 =
  let pos = BS.merge (positive pbs1) (positive pbs2) in
  let neg = BS.merge (negative pbs1) (negative pbs2) in
  if | BS.containsAnyFast pos neg -> Nothing
     | BS.containsAnyFast neg pos -> Nothing
     | otherwise ->
       Just (PolarizedBloomSeq { positive = pos, negative = neg })

-- | Size of positive sequence
sizePos :: PolarizedBloomSeq a -> Int
sizePos = BS.size . positive
{-# INLINE sizePos #-}

-- | Size of negative sequence
sizeNeg :: PolarizedBloomSeq a -> Int
sizeNeg = BS.size . negative
{-# INLINE sizeNeg #-}

-- | Total size (pos + neg)
totalSize :: PolarizedBloomSeq a -> Int
totalSize pbs = sizePos pbs + sizeNeg pbs
{-# INLINE totalSize #-}

-- | List of positive elements
toListPos :: PolarizedBloomSeq a -> [a]
toListPos = BS.toList . positive
{-# INLINE toListPos #-}

-- | List of negative elements
toListNeg :: PolarizedBloomSeq a -> [a]
toListNeg = BS.toList . negative
{-# INLINE toListNeg #-}

-- | All elements (pos ++ neg)
allElems :: PolarizedBloomSeq a -> [a]
allElems pbs = toListPos pbs ++ toListNeg pbs
{-# INLINE allElems #-}

-- | Check if both sequences are empty
isEmpty :: PolarizedBloomSeq a -> Bool
isEmpty pbs = BS.isEmpty (positive pbs) && BS.isEmpty (negative pbs)
{-# INLINE isEmpty #-}

-- | Hash a PolarizedBloomSeq using a custom hashing function
hashPBSWith :: (Int -> a -> Int) -> Int -> PolarizedBloomSeq a -> Int
hashPBSWith hashFn s pbs =
  let posElems = toListPos pbs
      negElems = toListNeg pbs
      s' = foldl hashFn s posElems
  in foldl hashFn s' negElems
{-# INLINE hashPBSWith #-}

-- | Hash a PolarizedBloomSeq with Hashable elements
hashPBS :: PC.Hashable a => Int -> PolarizedBloomSeq a -> Int
hashPBS = hashPBSWith PC.hashWithSalt
{-# INLINE hashPBS #-}

-- | Hash a PolarizedBloomSeq with HashableF elements
hashPBSF :: forall k (f :: k -> Type) (tp :: k). PC.HashableF f => Int -> PolarizedBloomSeq (f tp) -> Int
hashPBSF = hashPBSWith PC.hashWithSaltF
{-# INLINE hashPBSF #-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Who2.Expr.HashConsed.PolarizedExprSet
  ( PolarizedExprSet(..)
  , Simplified(..)
  , empty
  , insertIfNotPresent
  , fromTwo
  , merge
  , simplify
  , sizePos
  , sizeNeg
  , totalSize
  , toListPos
  , toListNeg
  , allElems
  , isEmpty
  , hashPESWith
  ) where

import Data.Hashable (Hashable(hashWithSalt))

import qualified Who2.Expr.HashConsed.ExprSet as ES
import qualified Who2.Expr.Bloom.Polarized as PBS
import Who2.Expr (HasId)

------------------------------------------------------------------------
-- Type and instances
------------------------------------------------------------------------

-- | Polarized set storing positive and negative elements in ExprSets
data PolarizedExprSet a = PolarizedExprSet
  { posSet :: !(ES.ExprSet a)
  , negSet :: !(ES.ExprSet a)
  }
  deriving (Eq, Ord, Show)

instance Hashable a => Hashable (PolarizedExprSet a) where
  hashWithSalt salt x = salt `hashWithSalt` posSet x `hashWithSalt` negSet x

------------------------------------------------------------------------
-- Operations
------------------------------------------------------------------------

-- | Simplified result
data Simplified a
  = Inconsistent
  | SinglePositive a
  | SingleNegative a
  | Merged (PolarizedExprSet a)

empty :: PolarizedExprSet a
empty = PolarizedExprSet ES.empty ES.empty
{-# INLINE empty #-}

insertIfNotPresent ::
  (HasId a, PBS.Polarizable a) =>
  PolarizedExprSet a ->
  a ->
  Maybe (PolarizedExprSet a)
insertIfNotPresent pset expr =
  case PBS.polarity expr of
    PBS.Positive inner ->
      if ES.member inner (negSet pset)
        then Nothing
        else Just $ pset { posSet = ES.insert inner (posSet pset) }
    PBS.Negative inner ->
      if ES.member inner (posSet pset)
        then Nothing
        else Just $ pset { negSet = ES.insert inner (negSet pset) }
{-# INLINE insertIfNotPresent #-}

fromTwo ::
  (HasId a, PBS.Polarizable a) =>
  a ->
  a ->
  Simplified a
fromTwo e1 e2 =
  case flip insertIfNotPresent e2 =<< insertIfNotPresent empty e1 of
    Nothing -> Inconsistent
    Just pset -> simplify pset
{-# INLINE fromTwo #-}

merge ::
  PolarizedExprSet a ->
  PolarizedExprSet a ->
  Maybe (PolarizedExprSet a)
merge pset1 pset2 =
  let mergedPos = ES.union (posSet pset1) (posSet pset2)
      mergedNeg = ES.union (negSet pset1) (negSet pset2)
      contradiction = not (ES.null (ES.intersection mergedPos mergedNeg))
  in if contradiction
     then Nothing
     else Just $ PolarizedExprSet mergedPos mergedNeg
{-# INLINE merge #-}

simplify :: PolarizedExprSet a -> Simplified a
simplify pset =
  case (ES.toList (posSet pset), ES.toList (negSet pset)) of
    ([], []) -> Inconsistent
    ([x], []) -> SinglePositive x
    ([], [x]) -> SingleNegative x
    _ -> Merged pset
{-# INLINE simplify #-}

toListPos :: PolarizedExprSet a -> [a]
toListPos pset = ES.toList (posSet pset)
{-# INLINE toListPos #-}

toListNeg :: PolarizedExprSet a -> [a]
toListNeg pset = ES.toList (negSet pset)
{-# INLINE toListNeg #-}

allElems :: PolarizedExprSet a -> [a]
allElems pset = toListPos pset ++ toListNeg pset
{-# INLINE allElems #-}

sizePos :: PolarizedExprSet a -> Int
sizePos pset = ES.size (posSet pset)
{-# INLINE sizePos #-}

sizeNeg :: PolarizedExprSet a -> Int
sizeNeg pset = ES.size (negSet pset)
{-# INLINE sizeNeg #-}

totalSize :: PolarizedExprSet a -> Int
totalSize pset = sizePos pset + sizeNeg pset
{-# INLINE totalSize #-}

isEmpty :: PolarizedExprSet a -> Bool
isEmpty pset = ES.null (posSet pset) && ES.null (negSet pset)
{-# INLINE isEmpty #-}

-- | Hash a PolarizedExprSet using a custom hashing function
hashPESWith :: (Int -> a -> Int) -> Int -> PolarizedExprSet a -> Int
hashPESWith hashFn s pset =
  let posElems = toListPos pset
      negElems = toListNeg pset
      s' = foldl hashFn s posElems
  in foldl hashFn s' negElems
{-# INLINE hashPESWith #-}

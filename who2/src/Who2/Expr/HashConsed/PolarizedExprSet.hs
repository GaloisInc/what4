{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}

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
  , eqBy
  , ordBy
  , hashPESWith
  ) where

import Prelude hiding (null)
import Data.Kind (Type)
import qualified What4.BaseTypes as BT

import qualified Who2.Expr.HashConsed.ExprSet as ES
import qualified Who2.Expr.Bloom.Polarized as PBS
import Who2.Expr (HasNonce)

-- | Polarized set storing positive and negative elements in ExprSets
data PolarizedExprSet (f :: BT.BaseType -> Type) (tp :: BT.BaseType) = PolarizedExprSet
  { posSet :: !(ES.ExprSet f tp)
  , negSet :: !(ES.ExprSet f tp)
  }

-- | Simplified result
data Simplified f tp
  = Inconsistent
  | SinglePositive (f tp)
  | SingleNegative (f tp)
  | Merged (PolarizedExprSet f tp)

empty :: PolarizedExprSet f tp
empty = PolarizedExprSet ES.empty ES.empty
{-# INLINE empty #-}

insertIfNotPresent ::
  (HasNonce f, PBS.Polarizable (f tp)) =>
  PolarizedExprSet f tp ->
  f tp ->
  Maybe (PolarizedExprSet f tp)
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
  (HasNonce f, PBS.Polarizable (f tp)) =>
  f tp ->
  f tp ->
  Simplified f tp
fromTwo e1 e2 =
  case flip insertIfNotPresent e2 =<< insertIfNotPresent empty e1 of
    Nothing -> Inconsistent
    Just pset -> simplify pset
{-# INLINE fromTwo #-}

merge ::
  PolarizedExprSet f tp ->
  PolarizedExprSet f tp ->
  Maybe (PolarizedExprSet f tp)
merge pset1 pset2 =
  let mergedPos = ES.union (posSet pset1) (posSet pset2)
      mergedNeg = ES.union (negSet pset1) (negSet pset2)
      contradiction = not (ES.null (ES.intersection mergedPos mergedNeg))
  in if contradiction
     then Nothing
     else Just $ PolarizedExprSet mergedPos mergedNeg
{-# INLINE merge #-}

simplify :: PolarizedExprSet f tp -> Simplified f tp
simplify pset =
  case (ES.toList (posSet pset), ES.toList (negSet pset)) of
    ([], []) -> Inconsistent
    ([x], []) -> SinglePositive x
    ([], [x]) -> SingleNegative x
    _ -> Merged pset
{-# INLINE simplify #-}

toListPos :: PolarizedExprSet f tp -> [f tp]
toListPos pset = ES.toList (posSet pset)
{-# INLINE toListPos #-}

toListNeg :: PolarizedExprSet f tp -> [f tp]
toListNeg pset = ES.toList (negSet pset)
{-# INLINE toListNeg #-}

allElems :: PolarizedExprSet f tp -> [f tp]
allElems pset = toListPos pset ++ toListNeg pset
{-# INLINE allElems #-}

sizePos :: PolarizedExprSet f tp -> Int
sizePos pset = ES.size (posSet pset)
{-# INLINE sizePos #-}

sizeNeg :: PolarizedExprSet f tp -> Int
sizeNeg pset = ES.size (negSet pset)
{-# INLINE sizeNeg #-}

totalSize :: PolarizedExprSet f tp -> Int
totalSize pset = sizePos pset + sizeNeg pset
{-# INLINE totalSize #-}

isEmpty :: PolarizedExprSet f tp -> Bool
isEmpty pset = ES.null (posSet pset) && ES.null (negSet pset)
{-# INLINE isEmpty #-}

eqBy :: (f tp -> f tp -> Bool) ->
        PolarizedExprSet f tp ->
        PolarizedExprSet f tp ->
        Bool
eqBy cmp x y =
  let posX = ES.toList (posSet x)
      posY = ES.toList (posSet y)
      negX = ES.toList (negSet x)
      negY = ES.toList (negSet y)
  in length posX == length posY && length negX == length negY &&
     all (\(a, b) -> cmp a b) (zip posX posY) &&
     all (\(a, b) -> cmp a b) (zip negX negY)

ordBy :: (f tp -> f tp -> Ordering) ->
         PolarizedExprSet f tp ->
         PolarizedExprSet f tp ->
         Ordering
ordBy cmp x y =
  let posX = ES.toList (posSet x)
      posY = ES.toList (posSet y)
  in case compareLists cmp posX posY of
       LT -> LT
       GT -> GT
       EQ -> compareLists cmp (ES.toList (negSet x)) (ES.toList (negSet y))
  where
    compareLists :: (a -> a -> Ordering) -> [a] -> [a] -> Ordering
    compareLists _ [] [] = EQ
    compareLists _ [] _  = LT
    compareLists _ _  [] = GT
    compareLists f (a:as) (b:bs) =
      case f a b of
        LT -> LT
        GT -> GT
        EQ -> compareLists f as bs

-- | Hash a PolarizedExprSet using a custom hashing function
hashPESWith :: (Int -> f tp -> Int) -> Int -> PolarizedExprSet f tp -> Int
hashPESWith hashFn s pset =
  let posElems = toListPos pset
      negElems = toListNeg pset
      s' = foldl hashFn s posElems
  in foldl hashFn s' negElems
{-# INLINE hashPESWith #-}

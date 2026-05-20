------------------------------------------------------------------------
-- |
-- Module           : What4.Utils.Arithmetic
-- Description      : Utility functions for computing arithmetic
-- Copyright        : (c) Galois, Inc 2015-2020
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedSums #-}
module What4.Utils.Arithmetic
  ( -- * Arithmetic utilities
    isPow2
  , isPow2Integer
  , lg
  , intLog2
  , lgCeil
  , intLogCeil
  , nextMultiple
  , nextPow2Multiple
  , tryIntSqrt
  , tryRationalSqrt
  , roundAway
  , ctz
  , clz
  , rotateLeft
  , rotateRight
  ) where

import Control.Exception (assert)
import Data.Bits (Bits(..))
import Data.Ratio

import Data.Parameterized.NatRepr

import What4.Utils.Arithmetic.Internal
  ( ctzOpt, clzOpt, intLog2Opt, isPow2IntegerOpt )

-- | Returns true if number is a power of two.
isPow2 :: (Bits a, Num a) => a -> Bool
isPow2 x = x .&. (x-1) == 0

-- | Returns true if Integer is a power of two. On GHC 9.0+ this uses a fast
-- primop from @ghc-bignum@; on earlier GHCs it falls back to 'isPow2'.
isPow2Integer :: Integer -> Bool
isPow2Integer = isPow2IntegerOpt
{-# INLINE isPow2Integer #-}

-- | Returns floor of log base 2. Polymorphic over bit-like types.
--
-- Note: For @Integer@ specifically, prefer 'intLog2' which uses fast primops
-- on GHC 9.0+.
lg :: (Bits a, Num a, Ord a) => a -> Int
lg i0 | i0 > 0 = go 0 (i0 `shiftR` 1)
      | otherwise = error "lg given number that is not positive."
  where go r 0 = r
        go r n = go (r+1) (n `shiftR` 1)

-- | @intLog2 n@ for @n >= 1@: floor of base-2 logarithm. Undefined for
-- @n <= 0@. On GHC 9.0+ this delegates to a fast primop in @ghc-bignum@;
-- on earlier GHCs it falls back to 'lg'.
intLog2 :: Integer -> Int
intLog2 = intLog2Opt
{-# INLINE intLog2 #-}

-- | Returns ceil of log base 2. Polymorphic over bit-like types.
--   We define @lgCeil 0 = 0@
--
-- Note: For @Integer@ specifically, prefer 'intLogCeil' which uses fast primops
-- on GHC 9.0+.
lgCeil :: (Bits a, Num a, Ord a) => a -> Int
lgCeil 0 = 0
lgCeil 1 = 0
lgCeil i | i > 1 = 1 + lg (i-1)
         | otherwise = error "lgCeil given number that is not positive."

-- | @intLogCeil n@ for @n >= 0@: ceiling of base-2 logarithm. We define
-- @intLogCeil 0 = 0@ and @intLogCeil 1 = 0@. On GHC 9.0+ this uses fast primops
-- from @ghc-bignum@; on earlier GHCs it falls back to 'lgCeil'.
intLogCeil :: Integer -> Int
intLogCeil 0 = 0
intLogCeil 1 = 0
intLogCeil i | i > 1 = 1 + intLog2 (i - 1)
             | otherwise = error "intLogCeil given number that is not positive."
{-# INLINE intLogCeil #-}

-- | Count trailing zeros
ctz :: NatRepr w -> Integer -> Integer
ctz = ctzOpt

-- | Count leading zeros
clz :: NatRepr w -> Integer -> Integer
clz = clzOpt

rotateRight ::
  NatRepr w {- ^ width -} ->
  Integer {- ^ value to rotate -} ->
  Integer {- ^ amount to rotate -} ->
  Integer
rotateRight w x n = xor (shiftR x' n') (toUnsigned w (shiftL x' (widthVal w - n')))
 where
 x' = toUnsigned w x
 n' = fromInteger (n `rem` intValue w)

rotateLeft ::
  NatRepr w {- ^ width -} ->
  Integer {- ^ value to rotate -} ->
  Integer {- ^ amount to rotate -} ->
  Integer
rotateLeft w x n = xor (shiftR x' (widthVal w - n')) (toUnsigned w (shiftL x' n'))
 where
 x' = toUnsigned w x
 n' = fromInteger (n `rem` intValue w)


-- | @nextMultiple x y@ computes the next multiple m of x s.t. m >= y.  E.g.,
-- nextMultiple 4 8 = 8 since 8 is a multiple of 8; nextMultiple 4 7 = 8;
-- nextMultiple 8 6 = 8.
nextMultiple :: Integral a => a -> a -> a
nextMultiple x y = ((y + x - 1) `div` x) * x

-- | @nextPow2Multiple x n@ returns the smallest multiple of @2^n@
-- not less than @x@.
nextPow2Multiple :: (Bits a, Integral a) => a -> Int -> a
nextPow2Multiple x n | x >= 0 && n >= 0 = ((x+2^n -1) `shiftR` n) `shiftL` n
                     | otherwise = error "nextPow2Multiple given negative value."

------------------------------------------------------------------------
-- Sqrt operators.

-- | This returns the sqrt of an integer if it is well-defined.
tryIntSqrt :: Integer -> Maybe Integer
tryIntSqrt 0 = return 0
tryIntSqrt 1 = return 1
tryIntSqrt 2 = Nothing
tryIntSqrt 3 = Nothing
tryIntSqrt n = assert (n >= 4) $ go (n `shiftR` 1)
  where go x | x2 < n  = Nothing   -- Guess is below sqrt, so we quit.
             | x2 == n = return x' -- We have found sqrt
             | True    = go x'     -- Guess is still too large, so try again.
          where -- Next guess is floor(avg(x, n/x))
                x' = (x + n `div` x) `div` 2
                x2 = x' * x'

-- | Return the rational sqrt of a
tryRationalSqrt :: Rational -> Maybe Rational
tryRationalSqrt r = do
  (%) <$> tryIntSqrt (numerator   r)
      <*> tryIntSqrt (denominator r)

------------------------------------------------------------------------
-- Conversion

-- | Evaluate a real to an integer with rounding away from zero.
roundAway :: (RealFrac a) => a -> Integer
roundAway r = truncate (r + signum r * 0.5)

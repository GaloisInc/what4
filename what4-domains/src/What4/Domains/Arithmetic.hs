------------------------------------------------------------------------
-- |
-- Module           : What4.Domains.Arithmetic
-- Description      : Utility functions for computing arithmetic
-- Copyright        : (c) Galois, Inc 2015-2020
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------
{-# LANGUAGE BangPatterns #-}
module What4.Domains.Arithmetic
  ( ctz
  , clz
  , countTrailingZerosOr0
  , intLog2
  , isPow2Integer
  , isPow2Natural
  , log2OfPowerOfTwo
  , bitsBelow
  , rotateLeft
  , rotateRight
  ) where

import qualified Control.Exception as X
import Data.Bits (Bits(..), xor, shiftL, shiftR, popCount)
import Numeric.Natural (Natural)

import Data.Parameterized.NatRepr

import What4.Domains.Arithmetic.Internal
  ( ctzOpt, clzOpt, intLog2Opt, isPow2IntegerOpt, isPow2NaturalOpt )

-- | /O(w)/. Count trailing zeros, capped at the width.
ctz :: NatRepr w -> Integer -> Integer
ctz = ctzOpt

-- | /O(w)/. Count leading zeros, capped at the width.
clz :: NatRepr w -> Integer -> Integer
clz = clzOpt

-- | /O(w)/. @intLog2 n@ for @n >= 1@: floor of base-2 logarithm. Undefined
-- for @n <= 0@. On GHC 9.0+ this delegates to a primop in @ghc-bignum@
-- (constant-time per limb); on earlier GHCs it uses a shift loop.
intLog2 :: Integer -> Int
intLog2 = intLog2Opt
{-# INLINE intLog2 #-}

-- | /O(w)/. Test whether @n@ is a positive power of two. On GHC 9.0+ this
-- uses the @integerIsPowerOf2#@ primop; on earlier GHCs it uses
-- @n .&. (n - 1) == 0@.
isPow2Integer :: Integer -> Bool
isPow2Integer = isPow2IntegerOpt
{-# INLINE isPow2Integer #-}

-- | /O(w)/. Test whether @n@ is a positive power of two. On GHC 9.0+ this
-- uses the @naturalIsPowerOf2#@ primop; on earlier GHCs it uses
-- @n .&. (n - 1) == 0@.
isPow2Natural :: Natural -> Bool
isPow2Natural = isPow2NaturalOpt
{-# INLINE isPow2Natural #-}

-- | /O(w)/. Count trailing zeros of a non-negative 'Integer', returning @0@
-- for input @0@. ('Data.Bits.countTrailingZeros' requires 'FiniteBits', which
-- 'Integer' doesn't have.)
--
-- Uses the bit-trick @popCount ((n .&. -n) - 1)@: @n .&. -n@ isolates the
-- lowest set bit (always a single power-of-two bit, for any nonzero @n@), and
-- @popCount@ of one less than that is the bit's position.
countTrailingZerosOr0 :: Integer -> Int
countTrailingZerosOr0 0 = 0
countTrailingZerosOr0 n = popCount ((n .&. negate n) - 1)
{-# INLINE countTrailingZerosOr0 #-}

-- | @log2OfPowerOfTwo n@ returns @k@ such that @n == 2^k@. Asserts that @n@
-- is a positive power of two, and that the fast computation
-- @popCount (n - 1)@ agrees with the general 'countTrailingZerosOr0'.
--
-- Faster than 'countTrailingZerosOr0' for known powers of two: skips the
-- @n .&. -n@ isolation step.
log2OfPowerOfTwo :: Integer -> Int
log2OfPowerOfTwo n =
  X.assert (isPow2Integer n) $
  X.assert (k == countTrailingZerosOr0 n) $
  k
  where
  k = popCount (n - 1)
{-# INLINE log2OfPowerOfTwo #-}

-- | /O(w)/. @bitsBelow n@ returns the smallest mask of the form @2^k - 1@
-- that is at least @n@. That is, @2^(floor(log2 n) + 1) - 1@ for @n > 0@,
-- or @0@ for @n <= 0@. Every value in @[0..n]@ has all its set bits within
-- this mask.
bitsBelow :: Integer -> Integer
bitsBelow n
  | n <= 0    = 0
  | otherwise = bit (intLog2 n + 1) - 1
{-# INLINE bitsBelow #-}

-- | /O(w)/. Rotate a @w@-bit value right by @n@ positions (mod @w@).
rotateRight ::
  NatRepr w {- ^ width -} ->
  Integer {- ^ value to rotate -} ->
  Integer {- ^ amount to rotate -} ->
  Integer
rotateRight w x n = xor (shiftR x' n') (toUnsigned w (shiftL x' (widthVal w - n')))
 where
 x' = toUnsigned w x
 n' = fromInteger (n `rem` intValue w)

-- | /O(w)/. Rotate a @w@-bit value left by @n@ positions (mod @w@).
rotateLeft ::
  NatRepr w {- ^ width -} ->
  Integer {- ^ value to rotate -} ->
  Integer {- ^ amount to rotate -} ->
  Integer
rotateLeft w x n = xor (shiftR x' (widthVal w - n')) (toUnsigned w (shiftL x' n'))
 where
 x' = toUnsigned w x
 n' = fromInteger (n `rem` intValue w)

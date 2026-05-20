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
  , intLog2
  , bitsBelow
  , rotateLeft
  , rotateRight
  ) where

import Data.Bits (Bits(..), xor, shiftL, shiftR)

import Data.Parameterized.NatRepr

import What4.Domains.Arithmetic.Internal
  ( ctzOpt, clzOpt, intLog2Opt )

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

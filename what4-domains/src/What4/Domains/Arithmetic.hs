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
  , rotateLeft
  , rotateRight
  ) where

import Data.Bits (Bits(..), xor, shiftL, shiftR)

import Data.Parameterized.NatRepr

-- | Count trailing zeros
ctz :: NatRepr w -> Integer -> Integer
ctz w x = go 0
 where
 go !i
   | i < toInteger (natValue w) && testBit x (fromInteger i) == False = go (i + 1)
   | otherwise = i

-- | Count leading zeros
clz :: NatRepr w -> Integer -> Integer
clz w x = go 0
 where
 go !i
   | i < toInteger (natValue w) && testBit x (widthVal w - fromInteger i - 1) == False = go (i + 1)
   | otherwise = i

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

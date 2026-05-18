{-|
Module      : What4.Domains.BV.Bitwise.Tnum
Copyright   : (c) Galois Inc, 2026
License     : BSD3
Maintainer  : langston@galois.com

Tristate-numbers as used in the eBPF verifier.

Used by the bitwise abstract domain to implement arithmetic operations.

A tristate number ('Tnum') is a pair of bitvectors @(v, m)@ where @v@ records
the bits known to be 1 and @m@ records the bits whose value is unknown. The two
are required to be disjoint. The set of concrete bitvectors represented by @(v,
m)@ is @{ v .|. (x .&. m) | x <- all bitvectors }@ — equivalently, the bitwise
abstract-domain element with bit-pattern bounds @(v, v .|. m)@.

This module is for internal use by 'What4.Domains.BV.Bitwise' only and is not
part of the public API.

See "Sound, Precise, and Fast Abstract Interpretation with Tristate Numbers"
https://arxiv.org/abs/2105.05398.
-}

{-# LANGUAGE BangPatterns #-}

module What4.Domains.BV.Bitwise.Tnum
  ( Tnum
  , tnumValue
  , tnumMask
  , mk
  , add
  , mul
  ) where

import qualified Control.Exception as X
import           Data.Bits

-- | A tristate-number representation.
--
-- The two fields are required to be disjoint (@tnumValue .&. tnumMask == 0@);
-- 'mk' enforces this with an 'X.assert'.
data Tnum = Tnum
  { tnumValue :: !Integer
    -- ^ The known-1 bits.
  , tnumMask  :: !Integer
    -- ^ The unknown bits.
  }

-- | Smart constructor that asserts the disjointness invariant.
mk :: Integer -> Integer -> Tnum
mk v m = X.assert (v .&. m == 0) (Tnum v m)
{-# INLINE mk #-}

-- | Tristate-number add, with the result truncated to @bvmask@.
add ::
  Integer {- ^ bvmask -} ->
  Tnum {- ^ a -} ->
  Tnum {- ^ b -} ->
  Tnum
add bvmask (Tnum av am) (Tnum bv bm) = mk resv resm
  where
  sm    = am + bm
  sv    = av + bv
  sigma = sm + sv
  chi   = sigma `xor` sv
  resm  = (chi .|. am .|. bm) .&. bvmask
  resv  = (sv .&. complement resm) .&. bvmask
{-# INLINE add #-}

-- | Tristate-number multiply, with the result truncated to @bvmask@.
mul ::
  Integer {- ^ bvmask -} ->
  Tnum {- ^ a -} ->
  Tnum {- ^ b -} ->
  Tnum
mul bvmask (Tnum av0 am0) (Tnum bv0 bm0) = go av0 am0 bv0 bm0 acc0
  where
  acc0 = mk ((av0 * bv0) .&. bvmask) 0
  -- Accumulate contributions from each bit of a. A known-1 bit at
  -- position i adds b's mask shifted into position i (b's value bits
  -- are already included via the initial @av*bv@ product). An unknown
  -- bit at position i adds (b.value | b.mask) shifted in, since the
  -- bit might or might not contribute b.
  go !av !am !bv !bm !acc
    | av == 0 && am == 0 = acc
    | otherwise =
        let acc'
              | testBit av 0 = add bvmask acc (Tnum 0 bm)
              | testBit am 0 = add bvmask acc (Tnum 0 (bv .|. bm))
              | otherwise    = acc
        in go (av `shiftR` 1) (am `shiftR` 1)
              (bv `shiftL` 1) (bm `shiftL` 1)
              acc'

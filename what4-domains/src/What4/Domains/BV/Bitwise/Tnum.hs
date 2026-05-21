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

For 'add' and 'mul', see "Sound, Precise, and Fast Abstract Interpretation with
Tristate Numbers" https://arxiv.org/abs/2105.05398.

For 'udiv' and 'urem', see "Program Analysis Combining Generalized Bit-Level
and Word-Level Abstractions " https://dl.acm.org/doi/abs/10.1145/3728905, and
especially their Clam code artifact https://zenodo.org/records/14001988.
-}

{-# LANGUAGE BangPatterns #-}

module What4.Domains.BV.Bitwise.Tnum
  ( Tnum
  , tnumValue
  , tnumMask
  , mk
  , add
  , mul
  , mulPrecise
  , udiv
  , urem
  ) where

import qualified Control.Exception as X
import           Data.Bits

import           What4.Domains.Arithmetic (bitsBelow, isPow2Integer)

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

-- | /O(w)/. Smart constructor that asserts the disjointness invariant
-- (@v .&. m == 0@).
mk :: Integer -> Integer -> Tnum
mk v m = X.assert (v .&. m == 0) (Tnum v m)
{-# INLINE mk #-}

-- | /O(w)/. Tristate-number add, with the result truncated to @bvmask@.
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

-- | /O(w)/. Tristate-number multiply via interval and trailing-zero analysis.
--
-- The result has:
--
--   * at least @ctzA + ctzB@ trailing zero bits, where @ctzA@ is the longest
--     prefix of low bits that are known-zero in @a@ (i.e.\ both 'tnumValue' and
--     'tnumMask' have that bit clear), and similarly for @ctzB@; and
--   * known bits derived from the arithmetic interval @[aMin*bMin, aMax*bMax]@
--     reduced modulo @bvmask+1@ (see 'wrappedKnownBitsOfInterval'). When the
--     interval fits within one modulus, bits above the highest disagreement
--     between the wrapped bounds are determined; when it crosses a modulus
--     boundary once, we recover bits the two halves agree on; if it spans a
--     full modulus, no high bits are determined.
--
-- Special case: when both operands are concrete singletons (mask == 0), the
-- result is the exact concrete product.
mul ::
  Integer {- ^ bvmask -} ->
  Tnum {- ^ a -} ->
  Tnum {- ^ b -} ->
  Tnum
mul bvmask (Tnum av am) (Tnum bv bm)
  | am == 0, bm == 0 = mk ((av * bv) .&. bvmask) 0
  | otherwise = mk (highValue .&. bvmask) (highUnknown .&. complement lowZeros .&. bvmask)
  where
  -- Trailing-zero analysis: ctz(value | mask) is the lowest bit that is not
  -- known-zero in each operand.
  ctzA = countTrailingZerosOr0 (av .|. am)
  ctzB = countTrailingZerosOr0 (bv .|. bm)
  lowZeros = (bit (ctzA + ctzB) - 1) .&. bvmask
  -- Interval analysis: the product lies in [aMin*bMin, aMax*bMax] (computed
  -- in unbounded Integer). 'wrappedKnownBitsOfInterval' reduces this modulo
  -- @bvmask+1@ and extracts known bits whether or not the interval crosses a
  -- modulus boundary.
  prodMin = av * bv
  prodMax = (av .|. am) * (bv .|. bm)
  (highValue, highUnknown) = wrappedKnownBitsOfInterval bvmask prodMin prodMax
{-# INLINE mul #-}

-- | /O(w)/. @knownBitsOfInterval lo hi@ analyzes the arithmetic interval @[lo, hi]@
-- (where @0 <= lo <= hi@) and returns @(value, mask)@ in tnum form: the bits
-- on which all values in @[lo, hi]@ agree are known (recorded in @value@),
-- and the bits below the highest disagreement are unknown (set in @mask@).
--
-- For example, if @lo = 0b1100@ and @hi = 0b1110@, every value in
-- @[lo, hi]@ has bits 3 and 2 set; bits 1 and 0 vary. So @value = 0b1100@
-- and @mask = 0b0011@.
--
-- This subsumes leading-zero analysis (when @lo = 0@) and adds leading-1
-- (and arbitrary leading-prefix) analysis when @lo > 0@.
knownBitsOfInterval :: Integer -> Integer -> (Integer, Integer)
knownBitsOfInterval lo hi = (lo .&. complement varying, varying)
  where
  -- Bits at-or-below the highest position where lo and hi disagree.
  varying = bitsBelow (lo `xor` hi)
{-# INLINE knownBitsOfInterval #-}

-- | /O(w)/. Like 'knownBitsOfInterval', but for the image of @[lo, hi]@ under
-- reduction modulo @bvmask + 1@ (where @0 <= lo <= hi@ and @bvmask@ is of the
-- form @2^w - 1@).
--
-- Three cases:
--
--   * @hi - lo + 1 >= bvmask + 1@: the image covers every residue, so no bits
--     are determined (returns @(0, bvmask)@).
--   * @lo \`quot\` (bvmask+1) == hi \`quot\` (bvmask+1)@: the interval fits
--     entirely within one modulus, so the wrapped bounds @lo \`rem\` (bvmask+1)@
--     and @hi \`rem\` (bvmask+1)@ are still ordered and we use
--     'knownBitsOfInterval' on them.
--   * Otherwise the interval crosses exactly one modulus boundary: the image is
--     @[wLo, bvmask] \\cup [0, wHi]@ where @wLo = lo \`rem\` (bvmask+1)@ and
--     @wHi = hi \`rem\` (bvmask+1)@. We analyze each half with
--     'knownBitsOfInterval' and join: a bit is known only when both halves
--     agree on it.
wrappedKnownBitsOfInterval :: Integer -> Integer -> Integer -> (Integer, Integer)
wrappedKnownBitsOfInterval bvmask lo hi
  | hi - lo >= modulus = (0, bvmask)
  | wLo <= wHi = knownBitsOfInterval wLo wHi
  | otherwise =
      let (vA, mA) = knownBitsOfInterval wLo bvmask
          (vB, mB) = knownBitsOfInterval 0 wHi
          mAB = mA .|. mB .|. (vA `xor` vB)
      in (vA .&. complement mAB, mAB)
  where
  modulus = bvmask + 1
  wLo = lo `rem` modulus
  wHi = hi `rem` modulus
{-# INLINE wrappedKnownBitsOfInterval #-}

-- | Count trailing zeros of a non-negative 'Integer', returning @0@ for input
-- @0@. ('Data.Bits.countTrailingZeros' requires 'FiniteBits', which 'Integer'
-- doesn't have.)
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

-- | /O(w²)/. Tristate-number multiply via shift-and-add (BPF
-- @tnum_mul@). The result is truncated to @bvmask@.
--
-- Strictly more precise than 'mul' on its own, but quadratic in @w@.
-- Captures bit-level structure of the product that trailing-zero
-- analysis can't see.
mulPrecise ::
  Integer {- ^ bvmask -} ->
  Tnum {- ^ a -} ->
  Tnum {- ^ b -} ->
  Tnum
mulPrecise bvmask (Tnum av0 am0) (Tnum bv0 bm0) = go av0 am0 bv0 bm0 acc0
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
{-# INLINE mulPrecise #-}

-- | /O(w)/. Tristate-number unsigned division, with the result truncated to
-- @bvmask@.
--
-- Assumes the divisor is nonzero. When the divisor is a known power of two,
-- the result is exact (a logical right shift); otherwise the result is bounded
-- by interval analysis: every bit above the highest disagreement between
-- @aMin \`quot\` bMax@ and @aMax \`quot\` bMin@ is determined.
udiv ::
  Integer {- ^ bvmask -} ->
  Tnum {- ^ a -} ->
  Tnum {- ^ b -} ->
  Tnum
udiv bvmask (Tnum av am) (Tnum bv bm)
  | bm == 0, isPow2Integer bv =
      let k = log2OfPowerOfTwo bv
      in mk ((av `shiftR` k) .&. bvmask) ((am `shiftR` k) .&. bvmask)
  | otherwise = mk (highValue .&. bvmask) (highUnknown .&. bvmask)
  where
  aMin = av .&. bvmask
  aMax = (av .|. am) .&. bvmask
  bMin = max 1 bv
  bMax = max 1 ((bv .|. bm) .&. bvmask)
  -- a / b lies in [aMin/bMax, aMax/bMin]. Both quotients are non-negative
  -- and within @bvmask@, so no overflow check is needed.
  qMin = aMin `quot` bMax
  qMax = aMax `quot` bMin
  (highValue, highUnknown) = knownBitsOfInterval qMin qMax
{-# INLINE udiv #-}

-- | /O(w)/. Tristate-number unsigned remainder, with the result truncated to
-- @bvmask@.
--
-- When the divisor is a known power of two, the result is exact (a bitwise
-- mask); otherwise the result is bounded by:
--
--   * leading-zero analysis on @min(aMax, bMax-1)@; and
--   * low-bit preservation: if the divisor has @k@ known trailing zeros
--     (i.e.\ is definitely divisible by @2^k@), then @x rem y@ preserves the
--     low @k@ bits of @x@.
urem ::
  Integer {- ^ bvmask -} ->
  Tnum {- ^ a -} ->
  Tnum {- ^ b -} ->
  Tnum
urem bvmask (Tnum av am) (Tnum bv bm)
  | bm == 0, isPow2Integer bv =
      let m = bv - 1
      in mk (av .&. m) (am .&. m)
  | otherwise =
      let highUnknown = bitsBelow rMax .&. bvmask
          -- If the divisor has k known trailing zeros (both value and mask
          -- bits are 0 in the low k positions), the remainder preserves the
          -- dividend's low k bits exactly.
          rhsTrailingZeros = countTrailingZerosOr0 (bv .|. bm)
          lowMask = (bit rhsTrailingZeros - 1) .&. bvmask
          lowValue = av .&. lowMask
          lowUnknown = am .&. lowMask
          resUnknown = (highUnknown .&. complement lowMask) .|. lowUnknown
          resValue = lowValue .&. complement resUnknown
      in mk (resValue .&. bvmask) (resUnknown .&. bvmask)
  where
  aMax = (av .|. am) .&. bvmask
  bMax = (bv .|. bm) .&. bvmask
  rMax = min aMax (max 0 (bMax - 1))
{-# INLINE urem #-}


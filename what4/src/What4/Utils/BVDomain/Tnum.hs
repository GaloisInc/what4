{-|
Module      : What4.Utils.BVDomain.Tnum
Copyright   : (c) Galois Inc, 2025
License     : BSD3
Maintainer  : langston@galois.com

Provides tnum (tristate number) abstract domain for bitvectors.

A tnum represents a set of bitvectors using value/mask pairs, where the mask
indicates unknown bits. This provides efficient bit-level precision for abstract
interpretation, particularly for bitwise operations.

Based on algorithms from:
- Linux eBPF verifier (tnum implementation)
- Clam static analyzer (crab/domains/tnum.hpp)
- "Signedness-Agnostic Program Analysis" (ISSTA 2025)

= Implementation Notes

This implementation closely follows the Clam reference with precision improvements:

* __Improved signed division__: The @sdiv@ operation now uses a circle-based
  approach (Clam tnum_impl.hpp:1007-1043) that splits operands into hemispheres
  and computes all 4 combinations, providing better precision for non-singleton
  divisors compared to the singleton-only approach.

* __Tnum-based shifts__: Added @shlTnum@, @lshrTnum@, and @ashrTnum@ operations
  that handle non-constant shift amounts (Clam tnum_impl.hpp:1297-1404). These
  compute over shift ranges with early bailout for large ranges.

* __Improved division precision__: The @udiv@ operation includes the
  @divComputeLowBit@ optimization from Clam (tnum_impl.hpp:868-908) to
  determine known trailing zero bits in division results.

* __Exact algorithm match__: Core operations (add, sub, mul, rem, shifts, etc.)
  precisely match the Clam reference implementation for maximum correctness.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module What4.Utils.BVDomain.Tnum
  ( -- * Tnum type
    Tnum(Tnum)
  , pattern TnumBottom
  , pattern TnumValue
  , bottom, top, singleton
  , isBottom, isTop, member, proper
  , width, bvdMask
  , fromRange
    -- * Lattice operations
  , join, meet, le
    -- * Arithmetic operations
  , add, neg, sub, mul
  , udiv, sdiv, urem, srem
    -- * Bitwise operations
  , and, or, xor, not
    -- * Shift operations
  , shl, lshr, ashr
  , shlTnum, lshrTnum, ashrTnum
    -- * Width operations
  , zext, sext, trunc
  , rol, ror
    -- * Helper functions
  , asSingleton
  , getCircles
  , fromRangeSigned
  , getZeroCircle, getOneCircle
    -- * Testing support
  , gen, genPair
    -- * Correctness properties
  , correct_singleton
  , correct_member
  , correct_from_range
  , correct_join
  , correct_meet
  , correct_le
  , correct_and
  , correct_or
  , correct_xor
  , correct_not
  , correct_shl
  , correct_lshr
  , correct_ashr
  , correct_add
  , correct_neg
  , correct_sub
  , correct_mul
  , correct_udiv
  , correct_sdiv
  , correct_urem
  , correct_srem
  , correct_zext
  , correct_sext
  , correct_trunc
  , correct_rol
  , correct_ror
    -- * Lattice properties
  , lattice_join_commutative
  , lattice_meet_commutative
  , lattice_join_associative
  , lattice_meet_associative
  , lattice_join_idempotent
  , lattice_meet_idempotent
  , lattice_absorption1
  , lattice_absorption2
  , lattice_le_reflexive
  , lattice_le_antisymmetric
  , lattice_le_transitive
  , lattice_join_upper_bound1
  , lattice_join_upper_bound2
  , lattice_meet_lower_bound1
  , lattice_meet_lower_bound2
  , lattice_join_least_upper_bound
  , lattice_meet_greatest_lower_bound
  ) where

import qualified Data.Bits as Bits
import           Data.Bits hiding (testBit, xor)
import           Data.Parameterized.NatRepr
import           GHC.TypeNats

import qualified Prelude
import           Prelude hiding (and, or, not)

import           Test.Verification ( Gen, chooseInteger, Property, property )

--------------------------------------------------------------------------------
-- Tnum definition

-- | A tnum (tristate number) represents a set of bitvectors using value/mask pairs.
--
-- Representation invariant: @value .&. mask == 0@
--
-- A concrete value @x@ is represented iff: @(x .&. complement mask) == value@
--
-- Intuition:
--   - @value@: The known bit values (where corresponding mask bit is 0)
--   - @mask@: The unknown bits (1 = unknown, 0 = known)
--
-- Example: @value=0b0100@, @mask=0b0011@ represents @{0b0100, 0b0101, 0b0110, 0b0111}@
--
-- Bottom (empty set) is represented implicitly when @value .&. mask /= 0@,
-- specifically when both @value@ and @mask@ are all ones (@2^w - 1@).

data Tnum (w :: Nat) = Tnum !(NatRepr w) !Integer !Integer
  -- ^ @Tnum width value mask@
  -- Stores width witness, known bit values, and unknown bit mask

deriving instance Show (Tnum w)

-- | Equality for tnums
instance Eq (Tnum w) where
  Tnum _ v1 m1 == Tnum _ v2 m2 = v1 == v2 && m1 == m2

-- | Pattern synonym for bottom (empty set)
--
-- Bottom is represented by violating the invariant: both value and mask are all ones.
-- This makes @value .&. mask /= 0@, which is impossible for valid tnums.
pattern TnumBottom :: NatRepr w -> Tnum w
pattern TnumBottom w <- (isBottomView -> Just w)
  where
    TnumBottom w =
      let all_ones = bit (fromIntegral (natValue w)) - 1
       in Tnum w all_ones all_ones

-- | View function for TnumBottom pattern
isBottomView :: Tnum w -> Maybe (NatRepr w)
isBottomView (Tnum w val msk)
  | (val .&. msk) /= 0 = Just w
  | otherwise = Nothing

-- | Pattern synonym for non-bottom tnums
--
-- Matches any tnum where the invariant holds: @value .&. mask == 0@
pattern TnumValue :: NatRepr w -> Integer -> Integer -> Tnum w
pattern TnumValue w val msk <- (isValueView -> Just (w, val, msk))
  where
    TnumValue w val msk
      | (val .&. msk) == 0 = Tnum w val msk
      | otherwise = error "TnumValue: invariant violated (value .&. mask /= 0)"

-- | View function for TnumValue pattern
isValueView :: Tnum w -> Maybe (NatRepr w, Integer, Integer)
isValueView (Tnum w val msk)
  | (val .&. msk) == 0 = Just (w, val, msk)
  | otherwise = Nothing

{-# COMPLETE TnumBottom, TnumValue #-}

--------------------------------------------------------------------------------
-- Basic operations

-- | Get the width witness from a tnum
width :: Tnum w -> NatRepr w
width (Tnum w _ _) = w

-- | Compute the mask for a given width: @2^w - 1@
bvdMask :: NatRepr w -> Integer
bvdMask w = bit (fromIntegral (natValue w)) - 1

-- | Bottom element (empty set)
-- Represented as value=all_ones, mask=all_ones (violates invariant)
bottom :: (1 <= w) => NatRepr w -> Tnum w
bottom w =
  let all_ones = bvdMask w
   in Tnum w all_ones all_ones

-- | Top element (all values)
top :: (1 <= w) => NatRepr w -> Tnum w
top w = Tnum w 0 (bvdMask w)

-- | Singleton tnum representing exactly one value
singleton :: (1 <= w) => NatRepr w -> Integer -> Tnum w
singleton w x = Tnum w (x .&. bvdMask w) 0

-- | Check if tnum is bottom
-- Bottom is represented by violating the invariant: value .&. mask /= 0
isBottom :: Tnum w -> Bool
isBottom (Tnum _ value mask) = (value .&. mask) /= 0

-- | Check if tnum is top
isTop :: Tnum w -> Bool
isTop t@(Tnum w value mask) =
  Prelude.not (isBottom t) && value == 0 && mask == bvdMask w

-- | Check if a value is a member of the tnum
member :: Tnum w -> Integer -> Bool
member t@(Tnum w value mask) x
  | isBottom t = False
  | otherwise =
      let x' = x .&. bvdMask w
       in (x' .&. complement mask) == value

-- | Check if tnum satisfies representation invariant
-- Note: bottom violates the invariant intentionally
proper :: Tnum w -> Bool
proper t@(Tnum w value mask) =
  let maxVal = bvdMask w
   in if isBottom t
      then True  -- Bottom is valid (special case)
      else value <= maxVal && mask <= maxVal && (value .&. mask == 0)

-- | Find leftmost set bit position (0-indexed from right)
fls :: Integer -> Int
fls 0 = 0
fls n = go 0 n
  where
    go pos 0 = pos
    go pos x = go (pos + 1) (x `shiftR` 1)

-- | Count minimum trailing zeros: minimum among all values in the tnum
countMinTrailingZeros :: (1 <= w) => Tnum w -> Int
countMinTrailingZeros (TnumBottom _) = 0
countMinTrailingZeros (TnumValue w value mask) =
  let maxVal = value + mask
   in go 0 maxVal
  where
    go pos n
      | Bits.testBit n 0 = pos
      | otherwise = go (pos + 1) (n `shiftR` 1)

-- | Count maximum trailing zeros: maximum among all values in the tnum
countMaxTrailingZeros :: (1 <= w) => Tnum w -> Int
countMaxTrailingZeros (TnumBottom _) = 0
countMaxTrailingZeros (TnumValue w value _) = go 0 value
  where
    go pos n
      | Bits.testBit n 0 = pos
      | otherwise = go (pos + 1) (n `shiftR` 1)

-- | Construct the tightest tnum representing all values in [@min@, @max@]
--
-- Algorithm from Clam tnum_impl.hpp lines 132-146.
fromRange :: (1 <= w) => NatRepr w -> Integer -> Integer -> Tnum w
fromRange w minVal maxVal
  | minVal > maxVal = bottom w
  | minVal == maxVal = singleton w minVal
  | otherwise =
      let widthMask = bvdMask w
          minVal' = minVal .&. widthMask
          maxVal' = maxVal .&. widthMask
          chi = minVal' `Bits.xor` maxVal'
          bits = fls chi
          widthInt = fromIntegral (natValue w) :: Int
       in if bits >= widthInt
          then top w
          else if bits == 0
          then singleton w minVal'
          else
            let delta = bit bits - 1
                value = minVal' .&. complement delta
                tnumMask = delta
             in TnumValue w value tnumMask

-- | Extract the zero circle (hemisphere 0: MSB=0, non-negative values).
--
-- Returns a tnum representing only the values in this tnum with MSB=0.
-- Based on Clam tnum_impl.hpp:202-219 (getZeroCircle).
getZeroCircle :: (1 <= w) => Tnum w -> Tnum w
getZeroCircle (TnumBottom w) = TnumBottom w
getZeroCircle t@(TnumValue w v m)
  | isBottom t = bottom w
  | otherwise =
      let widthInt = fromIntegral (natValue w) :: Int
          widthMask = bvdMask w
          msbMask = bit (widthInt - 1)
          -- Check if all values have MSB=0 (v has MSB=0 and m doesn't include MSB)
          vMsb = v .&. msbMask
          mMsb = m .&. msbMask
       in if vMsb == 0 && mMsb == 0
          then t  -- All values already in hemisphere 0
          else if vMsb /= 0 && mMsb == 0
          then bottom w  -- All values in hemisphere 1
          else -- m includes MSB, so values span both hemispheres
            -- Result is [v, v + (m & ~MSB)]
            let newMask = m .&. complement msbMask
             in TnumValue w v newMask

-- | Extract the one circle (hemisphere 1: MSB=1, negative values).
--
-- Returns a tnum representing only the values in this tnum with MSB=1.
-- Based on Clam tnum_impl.hpp:221-238 (getOneCircle).
getOneCircle :: (1 <= w) => Tnum w -> Tnum w
getOneCircle (TnumBottom w) = TnumBottom w
getOneCircle t@(TnumValue w v m)
  | isBottom t = bottom w
  | otherwise =
      let widthInt = fromIntegral (natValue w) :: Int
          widthMask = bvdMask w
          msbMask = bit (widthInt - 1)
          vMsb = v .&. msbMask
          mMsb = m .&. msbMask
       in if vMsb /= 0 && mMsb == 0
          then t  -- All values already in hemisphere 1
          else if vMsb == 0 && mMsb == 0
          then bottom w  -- All values in hemisphere 0
          else -- m includes MSB, so values span both hemispheres
            -- Result is [v + MSB, v + m]
            let newValue = v .|. msbMask
             in TnumValue w newValue m

--------------------------------------------------------------------------------
-- Lattice operations

-- | Lattice join (over-approximation, union)
join :: (1 <= w) => Tnum w -> Tnum w -> Tnum w
join (TnumBottom _) t2 = t2
join t1 (TnumBottom _) = t1
join (TnumValue w v1 m1) (TnumValue _ v2 m2) =
  let -- Combine masks: unknown if either is unknown
      mu = m1 .|. m2
      -- Find known bits that agree in both
      thisKnown = v1 .&. complement mu
      xKnown = v2 .&. complement mu
      -- Bits where known values disagree become unknown
      disagree = thisKnown `Bits.xor` xKnown
      -- Final mask includes original unknowns plus disagreements
      finalMask = mu .|. disagree
      -- Final value: known bits that agree
      finalValue = thisKnown .&. xKnown
   in TnumValue w finalValue finalMask

-- | Lattice meet (intersection)
meet :: (1 <= w) => Tnum w -> Tnum w -> Tnum w
meet (TnumBottom w) _ = TnumBottom w
meet _ (TnumBottom w) = TnumBottom w
meet (TnumValue w v1 m1) (TnumValue _ v2 m2) =
  let -- New mask: known if known in both
      newMask = m1 .&. m2
      -- New value: combine known bits
      newValue = (v1 .|. v2) .&. complement newMask
      -- Check consistency: where both are known, they must agree
      v1Known = v1 .|. m1
      v2Known = v2 .|. m2
      v1Masked = v1 .&. complement m2
      v2Masked = v2 .&. complement m1
   in if v1Known /= v2Known && v1Masked /= v2Masked
      then TnumBottom w
      else TnumValue w newValue newMask

-- | Subsumption test: @t1 `le` t2@ iff @t1@ represents a subset of @t2@
le :: Tnum w -> Tnum w -> Bool
le (TnumBottom _) _ = True
le _ (TnumBottom _) = False
le (TnumValue _ v1 m1) (TnumValue _ v2 m2) =
  -- t1 <= t2 iff t2's unknowns cover t1's unknowns and known bits agree
  (m1 .|. m2 == m2) && ((v1 `Bits.xor` v2) .&. complement m2 == 0)

--------------------------------------------------------------------------------
-- Arithmetic operations

-- | Addition with precise carry propagation.
--
-- Algorithm from Clam tnum_impl.hpp lines 746-762:
--   sm = m_mask + x.m_mask
--   sv = m_value + x.m_value
--   sigma = sm + sv
--   chi = sigma ^ sv
--   mu = chi | m_mask | x.m_mask
--   result = (sv & ~mu, mu)
--
-- The key insight: chi = (sm + sv) ^ sv tracks which bits become unknown
-- due to carry propagation through the unknown bits.
add :: (1 <= w) => Tnum w -> Tnum w -> Tnum w
add (TnumBottom w) _ = TnumBottom w
add _ (TnumBottom w) = TnumBottom w
add (TnumValue w v1 m1) (TnumValue _ v2 m2) =
  let widthMask = bvdMask w
      sm = (m1 + m2) .&. widthMask
      sv = (v1 + v2) .&. widthMask
      sigma = (sm + sv) .&. widthMask
      chi = sigma `Bits.xor` sv
      mu = (chi .|. m1 .|. m2) .&. widthMask
      value = sv .&. complement mu
   in TnumValue w value mu

-- | Subtraction with precise borrow propagation.
--
-- Algorithm from Clam tnum_impl.hpp lines 788-803:
--   dv = m_value - x.m_value
--   alpha = dv + m_mask
--   beta = dv - x.m_mask
--   chi = alpha ^ beta
--   mu = chi | m_mask | x.m_mask
--   result = (dv & ~mu, mu)
sub :: (1 <= w) => Tnum w -> Tnum w -> Tnum w
sub (TnumBottom w) _ = TnumBottom w
sub _ (TnumBottom w) = TnumBottom w
sub (TnumValue w v1 m1) (TnumValue _ v2 m2) =
  let widthMask = bvdMask w
      dv = (v1 - v2) .&. widthMask
      alpha = (dv + m1) .&. widthMask
      beta = (dv - m2) .&. widthMask
      chi = alpha `Bits.xor` beta
      mu = (chi .|. m1 .|. m2) .&. widthMask
      value = dv .&. complement mu
   in TnumValue w value mu

-- | Negation (two's complement).
--
-- Implemented as: @-x = 0 - x@ (following reference implementation)
neg :: (1 <= w) => Tnum w -> Tnum w
neg (TnumBottom w) = TnumBottom w
neg t@(TnumValue w _ _) = sub (singleton w 0) t

-- | Multiplication with shift-and-add algorithm.
--
-- Algorithm from Clam tnum_impl.hpp lines 828-854:
--   Implements a shift-and-add multiplier that tracks uncertainty:
--   1. acc_v = m_value * x.m_value (certain product)
--   2. acc_m accumulates uncertainty from unknown bits
--   3. For each bit position:
--        - If bit is known 1: add x_tmp.m_mask to uncertainty
--        - If bit is unknown: add (x_tmp.m_value | x_tmp.m_mask) to uncertainty
--        - Shift this_tmp right, x_tmp left
--   4. Combine certain product with accumulated uncertainty
mul :: (1 <= w) => Tnum w -> Tnum w -> Tnum w
mul (TnumBottom w) _ = TnumBottom w
mul _ (TnumBottom w) = TnumBottom w
mul t1@(TnumValue w v1 _) t2@(TnumValue _ v2 _)
  | isTop t1 || isTop t2 = top w
  | otherwise =
      let widthMask = bvdMask w
          accV = (v1 * v2) .&. widthMask
          -- Loop state: (this_tmp, x_tmp, acc_m)
          go thisTmp xTmp accMul
            | isBottom thisTmp || (asSingleton thisTmp == Just 0) = accMul
            | otherwise =
                case (thisTmp, xTmp) of
                  (TnumValue _ thisVal thisMask, TnumValue _ xVal xMask) ->
                    let -- Check lowest bit
                        thisLowBit = thisVal .&. 1
                        thisMaskLowBit = thisMask .&. 1
                        -- Accumulate uncertainty based on this bit
                        accMul' =
                          if thisLowBit /= 0
                          then add accMul (TnumValue w 0 xMask)
                          else if thisMaskLowBit /= 0
                          then add accMul (TnumValue w 0 (xVal .|. xMask))
                          else accMul
                        -- Shift operands
                        thisTmp' = lshr thisTmp 1
                        xTmp' = shl xTmp 1
                     in go thisTmp' xTmp' accMul'
                  _ -> accMul  -- Handle TnumBottom case (shouldn't happen due to guards)
          -- Start with zero uncertainty
          finalAccMul = go t1 t2 (singleton w 0)
          -- Combine certain product with uncertainty
          resTmp = TnumValue w accV 0
       in add resTmp finalAccMul

-- | Helper: check if tnum is a singleton and extract value
asSingleton :: Tnum w -> Maybe Integer
asSingleton (TnumBottom _) = Nothing
asSingleton (TnumValue _ value mask)
  | mask == 0 = Just value
  | otherwise = Nothing

-- | Count minimum leading zeros (leading zeros in value + mask)
countMinLeadingZeros :: (1 <= w) => Tnum w -> Int
countMinLeadingZeros (TnumBottom w) = fromIntegral (natValue w)
countMinLeadingZeros (TnumValue w value mask) =
  let widthInt = fromIntegral (natValue w) :: Int
      maxVal = value .|. mask
      leadingZeros = if maxVal == 0
                     then widthInt
                     else widthInt - fls maxVal
   in leadingZeros

-- | Test if tnum represents only non-negative values (MSB always 0)
isNonNegative :: (1 <= w) => Tnum w -> Bool
isNonNegative (TnumBottom _) = False
isNonNegative (TnumValue w value mask) =
  let widthInt = fromIntegral (natValue w) :: Int
      msbPos = widthInt - 1
   in Prelude.not (Bits.testBit mask msbPos) && Prelude.not (Bits.testBit value msbPos)

-- | Test if tnum represents only negative values (MSB always 1)
isNegative :: (1 <= w) => Tnum w -> Bool
isNegative (TnumBottom _) = False
isNegative (TnumValue w value mask) =
  let widthInt = fromIntegral (natValue w) :: Int
      msbPos = widthInt - 1
   in Prelude.not (Bits.testBit mask msbPos) && Bits.testBit value msbPos

-- | Get the signed maximum value represented by this tnum.
--
-- For signed interpretation: max = value + mask, but clear MSB if mask has MSB=1
-- (to stay within positive range).
-- Based on Clam tnum_impl.hpp:291-297.
getSignedMaxValue :: (1 <= w) => Tnum w -> Integer
getSignedMaxValue (TnumBottom _) = 0
getSignedMaxValue (TnumValue w value mask) =
  let widthInt = fromIntegral (natValue w) :: Int
      widthMask = bvdMask w
      msbPos = widthInt - 1
      maxVal = (value + mask) .&. widthMask
   in if Bits.testBit mask msbPos
      then Bits.clearBit maxVal msbPos
      else maxVal

-- | Get the signed minimum value represented by this tnum.
--
-- For signed interpretation: min = value, but set MSB if mask has MSB=1
-- (to enter negative range).
-- Based on Clam tnum_impl.hpp:299-313.
getSignedMinValue :: (1 <= w) => Tnum w -> Integer
getSignedMinValue (TnumBottom _) = 0
getSignedMinValue (TnumValue w value mask) =
  let widthInt = fromIntegral (natValue w) :: Int
      msbPos = widthInt - 1
      minVal = value
   in if Bits.testBit mask msbPos
      then Bits.setBit minVal msbPos
      else minVal

-- | Compute known low bits for division result.
--
-- Algorithm from Clam tnum_impl.hpp:868-908.
-- Determines trailing zero bits based on operand properties.
divComputeLowBit :: (1 <= w) => Tnum w -> Tnum w -> Tnum w -> Tnum w
divComputeLowBit known lhs rhs
  | isBottom known = top (width lhs)
  | otherwise =
      let widthMask = bvdMask (width lhs)
          widthInt = fromIntegral (natValue (width lhs)) :: Int

          -- If LHS is odd, result is odd
          known' = case (lhs, rhs) of
            (TnumValue _ v1 m1, _)
              | Bits.testBit v1 0 && Bits.testBit m1 0 ->
                  setBit known 0
            _ -> known

          -- Compute trailing zero bounds
          minTZ = countMinTrailingZeros lhs - countMaxTrailingZeros rhs
          maxTZ = countMaxTrailingZeros lhs - countMinTrailingZeros rhs

          known'' = if minTZ >= 0
                    then
                      let cleared = clearLowBits known' minTZ
                       in if minTZ == maxTZ
                          then setBit cleared minTZ
                          else cleared
                    else known'
       in if isBottom known'' then top (width lhs) else known''
  where
    setBit (TnumBottom w) _ = TnumBottom w
    setBit (TnumValue w v m) pos =
      TnumValue w (Bits.setBit v pos) (Bits.clearBit m pos)

    clearLowBits (TnumBottom w) _ = TnumBottom w
    clearLowBits (TnumValue w v m) n =
      let clearMask = complement ((bit n - 1) .&. bvdMask w)
       in TnumValue w (v .&. clearMask) (m .&. clearMask)

-- | Unsigned division with improved precision.
--
-- Uses divComputeLowBit optimization from Clam to determine known trailing zeros.
udiv :: (1 <= w) => Tnum w -> Tnum w -> Tnum w
udiv (TnumBottom w) _ = TnumBottom w
udiv _ (TnumBottom w) = TnumBottom w
udiv t1@(TnumValue w v1 m1) t2@(TnumValue _ v2 m2)
  | isTop t1 || isTop t2 = top w
  | v2 == 0 = top w  -- Division by zero
  | otherwise =
      case (asSingleton t1, asSingleton t2) of
        (Just x, Just y) | y /= 0 ->
          let widthMask = bvdMask w
              result = (x `div` y) .&. widthMask
           in singleton w result
        (_, Just _) ->
          -- Non-singleton dividend, singleton divisor
          let widthMask = bvdMask w
              widthInt = fromIntegral (natValue w) :: Int
              maxRes = (v1 + m1) `div` v2
              leadZ = countLeadingZeros widthInt maxRes
              -- Start with top, clear high bits
              res0 = clearHighBits (top w) leadZ
           in if leadZ == widthInt
              then res0
              else divComputeLowBit res0 t1 t2
        _ -> top w
  where
    countLeadingZeros widthInt n = go 0 n (widthInt - 1)
      where
        go count 0 _ = widthInt
        go count n pos
          | pos < 0 = count
          | Bits.testBit n pos = count
          | otherwise = go (count + 1) n (pos - 1)

    clearHighBits (TnumBottom w) _ = TnumBottom w
    clearHighBits (TnumValue w v m) n =
      let mask = (bit (fromIntegral (natValue w) - n) - 1) .&. bvdMask w
       in TnumValue w (v .&. mask) (m .&. mask)

-- | Signed division with improved precision using circle-based approach.
--
-- Splits operands into hemispheres and computes all 4 combinations:
-- - t0 / x0 (pos / pos = pos)
-- - t0 / x1 (pos / neg = neg)
-- - t1 / x0 (neg / pos = neg)
-- - t1 / x1 (neg / neg = pos, with overflow check)
--
-- Based on Clam tnum_impl.hpp:1007-1043.
sdiv :: (1 <= w) => Tnum w -> Tnum w -> Tnum w
sdiv (TnumBottom w) _ = TnumBottom w
sdiv _ (TnumBottom w) = TnumBottom w
sdiv t1@(TnumValue w _ _) t2@(TnumValue _ _ _)
  | isTop t1 || isTop t2 = top w
  | member t2 0 = top w  -- Division by possible zero
  | otherwise =
      let -- Split into hemispheres
          t0 = getZeroCircle t1  -- Non-negative dividend
          t1' = getOneCircle t1  -- Negative dividend
          x0 = getZeroCircle t2  -- Non-negative divisor
          x1 = getOneCircle t2   -- Negative divisor

          wInt = fromIntegral (natValue w) :: Int
          widthMask = bvdMask w
          half = bit (wInt - 1)

          -- Helper: signed division for singletons
          sdivSingleton a b =
            let toSigned n = if n >= half then n - bit wInt else n
                aSigned = toSigned a
                bSigned = toSigned b
                result = (aSigned `quot` bSigned) .&. widthMask
             in result

          -- Helper: signed division for tnums with enhanced analysis
          sdivTnum ta tb
            | isBottom ta || isBottom tb = bottom w
            | otherwise =
                case (asSingleton ta, asSingleton tb) of
                  (Just a, Just b) | b /= 0 -> singleton w (sdivSingleton a b)
                  _ -> -- Try to extract sign information for non-singletons
                       case (ta, tb) of
                         (TnumValue _ aVal aMask, TnumValue _ bVal bMask) ->
                           -- If both are non-negative, use unsigned division
                           if isNonNegative ta && isNonNegative tb
                           then udiv ta tb
                           else
                             let res = top w
                                 tmp = -- Compute a representative division result
                                   if isNegative ta && isNegative tb
                                   then -- neg / neg = pos (check for overflow)
                                        let aMin = getSignedMinValue ta
                                            bMax = getSignedMaxValue tb
                                            toSigned n = if n >= half then n - bit wInt else n
                                            aMinSigned = toSigned aMin
                                            bMaxSigned = toSigned bMax
                                         in if aMinSigned == -half && bMaxSigned == -1
                                            then 0  -- Overflow case, skip
                                            else if bMaxSigned /= 0
                                            then (aMinSigned `quot` bMaxSigned) .&. widthMask
                                            else 0
                                   else if isNegative ta && isNonNegative tb
                                   then -- neg / pos = neg (if magnitude is large enough)
                                        let aMax = getSignedMaxValue ta
                                            bMin = getSignedMinValue tb
                                            toSigned n = if n >= half then n - bit wInt else n
                                            aMaxSigned = toSigned aMax
                                            bMinSigned = toSigned bMin
                                         in if (-aMaxSigned) >= bMinSigned && bMinSigned /= 0
                                            then (aMaxSigned `quot` bMinSigned) .&. widthMask
                                            else 0
                                   else if isNonNegative ta && isNegative tb
                                   then -- pos / neg = neg (if magnitude is large enough)
                                        let aMin = getSignedMinValue ta
                                            bMax = getSignedMaxValue tb
                                            toSigned n = if n >= half then n - bit wInt else n
                                            aMinSigned = toSigned aMin
                                            bMaxSigned = toSigned bMax
                                         in if aMinSigned >= (-bMaxSigned) && bMaxSigned /= 0
                                            then (aMinSigned `quot` bMaxSigned) .&. widthMask
                                            else 0
                                   else 0
                              in if tmp /= 0
                                 then case res of
                                        TnumValue _ resVal resMask ->
                                          if Prelude.not (Bits.testBit tmp (wInt - 1))
                                          then -- Result is positive, clear leading bits
                                               let leadZ = if tmp == 0 then wInt else wInt - fls tmp
                                                   clearMask = (bit (wInt - leadZ) - 1) .&. widthMask
                                                in TnumValue w (resVal .&. clearMask) (resMask .&. clearMask)
                                          else -- Result is negative, set leading bits
                                               let leadOne = wInt - fls (complement tmp .&. widthMask)
                                                   highBits = ((bit leadOne - 1) `shiftL` (wInt - leadOne)) .&. widthMask
                                                   clearMask = (bit (wInt - leadOne) - 1) .&. widthMask
                                                in TnumValue w ((resVal .|. highBits) .&. widthMask) (resMask .&. clearMask)
                                        _ -> res
                                 else res
                         _ -> top w

          -- Compute all combinations
          res00 = sdivTnum t0 x0   -- pos / pos
          res01 = sdivTnum t0 x1   -- pos / neg
          res10 = sdivTnum t1' x0  -- neg / pos
          res11 = sdivTnum t1' x1  -- neg / neg (with overflow check)

          -- Join all results
       in join res00 (join res01 (join res10 res11))

-- | Unsigned remainder with improved precision.
--
-- Optimized for power-of-2 divisors following clam algorithm.
urem :: (1 <= w) => Tnum w -> Tnum w -> Tnum w
urem (TnumBottom w) _ = TnumBottom w
urem _ (TnumBottom w) = TnumBottom w
urem t1@(TnumValue w v1 m1) t2@(TnumValue _ v2 m2)
  | isTop t1 || isTop t2 = top w
  | v2 == 0 = top w  -- Division by zero
  | otherwise =
      case (asSingleton t1, asSingleton t2) of
        (Just x, Just y) | y /= 0 ->
          let widthMask = bvdMask w
              result = (x `mod` y) .&. widthMask
           in singleton w result
        (_, Just y) | y /= 0 && Bits.popCount y == 1 ->
          -- Divisor is a power of 2: x % 2^k = x & (2^k - 1)
          let maskLow = y - 1
              resValue = v1 .&. maskLow
              resMask = m1 .&. maskLow
           in TnumValue w resValue resMask
        _ -> top w

-- | Signed remainder (conservative - returns top unless both are singletons)
srem :: (1 <= w) => Tnum w -> Tnum w -> Tnum w
srem (TnumBottom w) _ = TnumBottom w
srem _ (TnumBottom w) = TnumBottom w
srem t1@(TnumValue w _ _) t2@(TnumValue _ _ _)
  | isTop t1 || isTop t2 = top w
  | otherwise =
      case (asSingleton t1, asSingleton t2) of
        (Just x, Just y) | y /= 0 ->
          let widthMask = bvdMask w
              wInt = fromIntegral (natValue w) :: Int
              -- Convert to signed
              toSigned n = if Bits.testBit n (wInt - 1)
                          then n - bit wInt
                          else n
              xSigned = toSigned x
              ySigned = toSigned y
              -- Use rem (not mod) for signed remainder: sign follows dividend
              result = (xSigned `rem` ySigned) .&. widthMask
           in singleton w result
        _ -> top w

--------------------------------------------------------------------------------
-- Bitwise operations

-- | Bitwise AND operation on tnums.
--
-- A bit is known to be 0 in the result iff at least one input has that bit as known 0.
-- A bit is known to be 1 in the result iff both inputs have that bit as known 1.
and :: (1 <= w) => Tnum w -> Tnum w -> Tnum w
and (TnumBottom w) _ = TnumBottom w
and _ (TnumBottom w) = TnumBottom w
and (TnumValue w v1 m1) (TnumValue _ v2 m2) =
  let -- A bit is known 0 if: at least one input has it as known 0
      -- Known 0 in t1: ~m1 & ~v1
      -- Known 0 in t2: ~m2 & ~v2
      known0 = (complement m1 .&. complement v1) .|. (complement m2 .&. complement v2)

      -- A bit is known 1 if: both inputs have it as known 1
      -- Known 1 in t1: ~m1 & v1
      -- Known 1 in t2: ~m2 & v2
      known1 = (complement m1 .&. v1) .&. (complement m2 .&. v2)

      -- Mask: bits that are neither known 0 nor known 1
      mask = complement (known0 .|. known1)

      -- Value: known 1 bits
      value = known1

   in TnumValue w value mask

-- | Bitwise OR operation on tnums.
--
-- A bit is known to be 1 in the result iff at least one input has that bit as known 1.
-- A bit is known to be 0 in the result iff both inputs have that bit as known 0.
or :: (1 <= w) => Tnum w -> Tnum w -> Tnum w
or (TnumBottom w) _ = TnumBottom w
or _ (TnumBottom w) = TnumBottom w
or (TnumValue w v1 m1) (TnumValue _ v2 m2) =
  let -- A bit is known 1 if: at least one input has it as known 1
      -- Known 1 in t1: ~m1 & v1
      -- Known 1 in t2: ~m2 & v2
      known1 = (complement m1 .&. v1) .|. (complement m2 .&. v2)

      -- A bit is known 0 if: both inputs have it as known 0
      -- Known 0 in t1: ~m1 & ~v1
      -- Known 0 in t2: ~m2 & ~v2
      known0 = (complement m1 .&. complement v1) .&. (complement m2 .&. complement v2)

      -- Mask: bits that are neither known 0 nor known 1
      mask = complement (known0 .|. known1)

      -- Value: known 1 bits
      value = known1

   in TnumValue w value mask

-- | Bitwise XOR operation on tnums.
--
-- A bit is known in the result iff both inputs have that bit known.
-- The value is the XOR of the two known values.
xor :: (1 <= w) => Tnum w -> Tnum w -> Tnum w
xor (TnumBottom w) _ = TnumBottom w
xor _ (TnumBottom w) = TnumBottom w
xor (TnumValue w v1 m1) (TnumValue _ v2 m2) =
  let -- Mask: unknown if either input is unknown
      mask = m1 .|. m2
      -- Value: XOR of known values, cleared where unknown
      value = (v1 `Bits.xor` v2) .&. complement mask
   in TnumValue w value mask

-- | Bitwise NOT operation on tnums.
--
-- Flips all known bits; unknown bits stay unknown.
not :: (1 <= w) => Tnum w -> Tnum w
not (TnumBottom w) = TnumBottom w
not (TnumValue w value mask) =
  let widthMask = bvdMask w
      -- Flip value bits (within width)
      newValue = (complement value .&. widthMask) .&. complement mask
   in TnumValue w newValue mask

--------------------------------------------------------------------------------
-- Shift operations

-- | Logical left shift by constant.
shl :: (1 <= w) => Tnum w -> Integer -> Tnum w
shl (TnumBottom w) _ = TnumBottom w
shl (TnumValue w value mask) k =
  let widthMask = bvdMask w
      k' = fromIntegral k :: Int
      newValue = (value `shiftL` k') .&. widthMask
      newMask = (mask `shiftL` k') .&. widthMask
   in TnumValue w newValue newMask

-- | Logical right shift by constant.
lshr :: (1 <= w) => Tnum w -> Integer -> Tnum w
lshr (TnumBottom w) _ = TnumBottom w
lshr (TnumValue w value mask) k =
  let k' = fromIntegral k :: Int
      newValue = value `shiftR` k'
      newMask = mask `shiftR` k'
   in TnumValue w newValue newMask

-- | Arithmetic right shift by constant.
--
-- If MSB is known, use its value to determine sign extension.
-- If MSB is unknown, conservatively join both possibilities.
ashr :: (1 <= w) => Tnum w -> Integer -> Tnum w
ashr (TnumBottom w) _ = TnumBottom w
ashr (TnumValue w value mask) k =
  let widthInt = fromIntegral (natValue w) :: Int
      k' = fromIntegral k :: Int
      msbPos = widthInt - 1
      valueMsb = Bits.testBit value msbPos
      maskMsb = Bits.testBit mask msbPos
   in if Prelude.not maskMsb && Prelude.not valueMsb
      then -- MSB known to be 0: logical shift
        TnumValue w (value `shiftR` k') (mask `shiftR` k')
      else if Prelude.not maskMsb && valueMsb
      then -- MSB known to be 1: sign extend
        let signExtMask = (bvdMask w `shiftL` (widthInt - k')) .&. bvdMask w
            newValue = (value `shiftR` k') .|. signExtMask
            newMask = mask `shiftR` k'
         in TnumValue w newValue newMask
      else -- MSB unknown: join both possibilities
        let -- Case 1: MSB=0 (logical shift)
            -- Clear MSB from mask since we're treating it as known in this case
            mask0 = mask .&. complement (bit msbPos)
            t0 = TnumValue w ((value .&. complement (bit msbPos)) `shiftR` k') (mask0 `shiftR` k')
            -- Case 2: MSB=1 (arithmetic shift)
            -- Clear MSB from mask since we're treating it as known in this case
            mask1 = mask .&. complement (bit msbPos)
            signExtMask = (bvdMask w `shiftL` (widthInt - k')) .&. bvdMask w
            value1 = (value .|. bit msbPos) `shiftR` k'
            t1 = TnumValue w (value1 .|. signExtMask) (mask1 `shiftR` k')
         in join t0 t1

-- | Logical left shift by tnum (non-constant shift amount).
--
-- Handles shift amounts that may not be constant.
-- Based on Clam tnum_impl.hpp:1211-1266 with precision optimizations.
shlTnum :: (1 <= w) => Tnum w -> Tnum w -> Tnum w
shlTnum (TnumBottom w) _ = TnumBottom w
shlTnum _ (TnumBottom w) = TnumBottom w
shlTnum tx@(TnumValue w xVal xMask) tk@(TnumValue _ kVal kMask)
  -- If shift is singleton, use constant shift
  | Just k <- asSingleton tk = shl tx k
  -- Fast path: if LHS is completely unknown (all bits unknown)
  | xMask == bvdMask w =
      let minShift = fromIntegral kVal :: Int
       in TnumValue w 0 ((bvdMask w) `shiftL` minShift .&. bvdMask w)
  -- Otherwise, compute over range [k.value, k.value + k.mask]
  | otherwise =
      let widthInt = fromIntegral (natValue w) :: Int
          widthMask = bvdMask w
          minShift = kVal
          maxShift = kVal + kMask
          maxShiftClamped = min maxShift (fromIntegral widthInt)

          -- Optimization: compute leading zeros of max possible value
          maxValue = xVal .|. xMask
          leadingZeros = if maxValue == 0
                         then widthInt
                         else widthInt - fls maxValue

          -- Special case: shift range is [0, w] - use trailing zeros
          minTrailingZeros = countMinTrailingZeros tx
       in if minShift == 0 && maxShiftClamped == fromIntegral widthInt
          then -- Full range shift: preserve trailing zeros
               let newVal = 0
                   newMask = bvdMask w
                   -- Clear the known trailing zero bits
                   clearedMask = if minTrailingZeros > 0
                                 then newMask .&. complement ((bit minTrailingZeros - 1) .&. widthMask)
                                 else newMask
                in TnumValue w newVal clearedMask
          else if maxShift - minShift > 8 || maxShift >= fromIntegral widthInt
          then top w
          else -- Join results for all shift amounts in range
               -- Optimization: skip shift amounts that cannot occur
               let isShiftPossible i =
                     let iMasked = i .&. kMask
                      in (kVal .|. kMask) == (kVal .|. iMasked)
                   shifts = [minShift..maxShiftClamped]
                   validShifts = filter isShiftPossible shifts
                   results = map (shl tx . fromIntegral) validShifts
                   joinedResult = foldl join (bottom w) results
                   -- Apply leading zero optimization to result
                   joinedWithLeadingZeros =
                     case joinedResult of
                       TnumBottom _ -> joinedResult
                       TnumValue _ jVal jMask ->
                         let highBitsToClear = leadingZeros - fromIntegral maxShiftClamped
                          in if highBitsToClear > 0
                             then let clearHighMask = complement (((bit widthInt - 1) `shiftL` (widthInt - highBitsToClear)) .&. widthMask)
                                   in TnumValue w (jVal .&. clearHighMask) (jMask .&. clearHighMask)
                             else joinedResult
                in if isBottom joinedWithLeadingZeros
                   then top w
                   else joinedWithLeadingZeros

-- | Logical right shift by tnum (non-constant shift amount).
--
-- Based on Clam tnum_impl.hpp:1268-1322 with precision optimizations.
lshrTnum :: (1 <= w) => Tnum w -> Tnum w -> Tnum w
lshrTnum (TnumBottom w) _ = TnumBottom w
lshrTnum _ (TnumBottom w) = TnumBottom w
lshrTnum tx@(TnumValue w xVal xMask) tk@(TnumValue _ kVal kMask)
  | Just k <- asSingleton tk = lshr tx k
  | otherwise =
      let widthInt = fromIntegral (natValue w) :: Int
          widthMask = bvdMask w
          minShift = kVal
          maxShift = kVal + kMask
          maxShiftClamped = min maxShift (fromIntegral widthInt)

          -- Optimization: compute leading zeros of value (not value|mask for lshr)
          leadingZerosOfValue = if xVal == 0
                                then widthInt
                                else widthInt - fls xVal

          -- If all bits will be shifted out, return zero
       in if leadingZerosOfValue + fromIntegral minShift >= widthInt
          then singleton w 0
          else if maxShift - minShift > 8 || maxShift >= fromIntegral widthInt
          then -- Return top but with leading zero optimization
               let highBitsToClear = leadingZerosOfValue + fromIntegral minShift
                in if highBitsToClear >= widthInt
                   then singleton w 0
                   else let clearMask = (bit (widthInt - highBitsToClear) - 1) .&. widthMask
                         in TnumValue w 0 clearMask
          else let shifts = [minShift..maxShiftClamped]
                   results = map (lshr tx . fromIntegral) shifts
                   joinedResult = foldl join (bottom w) results
                   -- Apply leading zero optimization
                   optimizedResult =
                     case joinedResult of
                       TnumBottom _ -> joinedResult
                       TnumValue _ jVal jMask ->
                         let highBitsToClear = leadingZerosOfValue + fromIntegral minShift
                          in if highBitsToClear >= widthInt
                             then singleton w 0
                             else let clearMask = (bit (widthInt - highBitsToClear) - 1) .&. widthMask
                                   in TnumValue w (jVal .&. clearMask) (jMask .&. clearMask)
                in if isBottom optimizedResult
                   then case optimizedResult of
                          TnumBottom _ ->
                            let highBitsToClear = leadingZerosOfValue + fromIntegral minShift
                             in if highBitsToClear >= widthInt
                                then singleton w 0
                                else TnumValue w 0 ((bit (widthInt - highBitsToClear) - 1) .&. widthMask)
                          _ -> optimizedResult
                   else optimizedResult

-- | Arithmetic right shift by tnum (non-constant shift amount).
--
-- Based on Clam tnum_impl.hpp:1324-1373 with precision optimizations.
ashrTnum :: (1 <= w) => Tnum w -> Tnum w -> Tnum w
ashrTnum (TnumBottom w) _ = TnumBottom w
ashrTnum _ (TnumBottom w) = TnumBottom w
ashrTnum tx@(TnumValue w xVal xMask) tk@(TnumValue _ kVal kMask)
  | Just k <- asSingleton tk = ashr tx k
  | otherwise =
      let widthInt = fromIntegral (natValue w) :: Int
          widthMask = bvdMask w
          minShift = kVal
          maxShift = kVal + kMask
          maxShiftClamped = min maxShift (fromIntegral widthInt)

          -- Optimization: compute leading zeros of value
          leadingZerosOfValue = if xVal == 0
                                then widthInt
                                else widthInt - fls xVal

          -- If value has enough leading zeros, result is all zeros or all ones
       in if leadingZerosOfValue >= widthInt
          then singleton w 0
          else if maxShift - minShift > 8 || maxShift >= fromIntegral widthInt
          then -- Return top with leading zero optimization
               let clearMask = (bit (widthInt - leadingZerosOfValue) - 1) .&. widthMask
                in TnumValue w 0 clearMask
          else let shifts = [minShift..maxShiftClamped]
                   results = map (ashr tx . fromIntegral) shifts
                   joinedResult = foldl join (bottom w) results
                   -- Apply leading zero optimization
                   optimizedResult =
                     case joinedResult of
                       TnumBottom _ -> joinedResult
                       TnumValue _ jVal jMask ->
                         let clearMask = (bit (widthInt - leadingZerosOfValue) - 1) .&. widthMask
                          in TnumValue w (jVal .&. clearMask) (jMask .&. clearMask)
                in if isBottom optimizedResult
                   then case optimizedResult of
                          TnumBottom _ ->
                            let clearMask = (bit (widthInt - leadingZerosOfValue) - 1) .&. widthMask
                             in TnumValue w 0 clearMask
                          _ -> optimizedResult
                   else optimizedResult

--------------------------------------------------------------------------------
-- Width operations

-- | Zero extension: extend with 0s in high bits.
zext :: (1 <= w, w+1 <= u) => Tnum w -> NatRepr u -> Tnum u
zext (TnumBottom _) u = TnumBottom u
zext (TnumValue _ value mask) u =
  -- Value and mask stay the same, just in wider type
  TnumValue u value mask

-- | Sign extension: extend with sign bit in high bits.
--
-- Applies sign extension to both value and mask, following clam's algorithm.
-- This is more precise than returning top when sign bit is unknown.
sext :: (1 <= w, 1 <= u, w+1 <= u) => Tnum w -> NatRepr u -> Tnum u
sext (TnumBottom _) u = TnumBottom u
sext (TnumValue w value mask) u =
  let widthInt = fromIntegral (natValue w) :: Int
      newWidthInt = fromIntegral (natValue u) :: Int
      extBits = newWidthInt - widthInt
      msbPos = widthInt - 1
      -- Sign extend value: replicate MSB into high bits
      valueSigned = if Bits.testBit value msbPos
                    then value .|. (((bit extBits - 1) `shiftL` widthInt))
                    else value
      -- Sign extend mask: replicate MSB of mask into high bits
      maskSigned = if Bits.testBit mask msbPos
                   then mask .|. (((bit extBits - 1) `shiftL` widthInt))
                   else mask
   in TnumValue u valueSigned maskSigned

-- | Truncation: keep only low n bits.
trunc :: (1 <= n, n+1 <= w) => NatRepr n -> Tnum w -> Tnum n
trunc n (TnumBottom _) = TnumBottom n
trunc n (TnumValue _ value mask) =
  let newMask = bvdMask n
      newValue = value .&. newMask
      newUnknowns = mask .&. newMask
   in TnumValue n newValue newUnknowns

-- | Rotate left.
rol :: (1 <= w) => Tnum w -> Integer -> Tnum w
rol (TnumBottom w) _ = TnumBottom w
rol (TnumValue w value mask) k =
  let widthInt = fromIntegral (natValue w) :: Int
      k' = fromIntegral (k `mod` fromIntegral widthInt) :: Int
      widthMask = bvdMask w
      newValue = ((value `shiftL` k') .|. (value `shiftR` (widthInt - k'))) .&. widthMask
      newMask = ((mask `shiftL` k') .|. (mask `shiftR` (widthInt - k'))) .&. widthMask
   in TnumValue w newValue newMask

-- | Rotate right.
ror :: (1 <= w) => Tnum w -> Integer -> Tnum w
ror (TnumBottom w) _ = TnumBottom w
ror (TnumValue w value mask) k =
  let widthInt = fromIntegral (natValue w) :: Int
      k' = fromIntegral (k `mod` fromIntegral widthInt) :: Int
      widthMask = bvdMask w
      newValue = ((value `shiftR` k') .|. (value `shiftL` (widthInt - k'))) .&. widthMask
      newMask = ((mask `shiftR` k') .|. (mask `shiftL` (widthInt - k'))) .&. widthMask
   in TnumValue w newValue newMask

--------------------------------------------------------------------------------
-- Helper functions

-- | Extract hemispheres from a tnum by splitting at MSB.
--
-- Returns (hemisphere0, hemisphere1) where:
-- - hemisphere0: values with MSB=0
-- - hemisphere1: values with MSB=1
getCircles :: (1 <= w) => Tnum w -> (Tnum w, Tnum w)
getCircles (TnumBottom w) = (TnumBottom w, TnumBottom w)
getCircles t@(TnumValue w value mask) =
  let widthInt = fromIntegral (natValue w) :: Int
      msbPos = widthInt - 1
      msbKnown = Prelude.not (Bits.testBit mask msbPos)
      msbValue = Bits.testBit value msbPos
   in if msbKnown
      then if msbValue
           then (TnumBottom w, t)  -- All in hemisphere 1
           else (t, TnumBottom w)  -- All in hemisphere 0
      else -- MSB unknown: split into both hemispheres
           let hemi0Value = value .&. complement (bit msbPos)
               hemi0Mask = mask .&. complement (bit msbPos)
               hemi1Value = (value .|. bit msbPos) .&. complement hemi0Mask
               hemi1Mask = hemi0Mask
            in (TnumValue w hemi0Value hemi0Mask,
                TnumValue w hemi1Value hemi1Mask)

-- | Helper: fromRange for signed values (handles MSB specially).
--
-- Similar to fromRange but used when constructing tnums within a single hemisphere
-- for signed operations. When bits > w-1, returns a special tnum that represents
-- all values in the hemisphere.
fromRangeSigned :: (1 <= w) => NatRepr w -> Integer -> Integer -> Tnum w
fromRangeSigned w minVal maxVal
  | minVal > maxVal = TnumBottom w
  | minVal == maxVal = singleton w minVal
  | otherwise =
      let widthMask = bvdMask w
          minVal' = minVal .&. widthMask
          maxVal' = maxVal .&. widthMask
          chi = minVal' `Bits.xor` maxVal'
          bits = fls chi
          widthInt = fromIntegral (natValue w) :: Int
       in if bits > widthInt - 1
          then -- Range spans full hemisphere
               let msbSet = Bits.testBit minVal' (widthInt - 1)
                   signedMax = bit (widthInt - 1) - 1
                in if msbSet
                   then -- Negative hemisphere: [signedMin, -1]
                        TnumValue w (bit (widthInt - 1)) signedMax
                   else -- Non-negative hemisphere: [0, signedMax]
                        TnumValue w 0 signedMax
          else -- Normal case
               let delta = bit bits - 1
                   value = minVal' .&. complement delta
                   tnumMask = delta
                in TnumValue w value tnumMask

--------------------------------------------------------------------------------
-- Test support

-- | Generate random tnum
gen :: (1 <= w) => NatRepr w -> Gen (Tnum w)
gen w = do
  r <- chooseInteger (0, 10)
  if r == 0
    then Prelude.pure $ bottom w
    else if r == 1
    then Prelude.pure $ top w
    else do
      value <- chooseInteger (0, bvdMask w)
      mask <- chooseInteger (0, bvdMask w)
      let validValue = value .&. complement mask
      Prelude.pure $ Tnum w validValue mask

-- | Generate tnum and a member of that tnum
-- Never generates bottom (always generates a tnum with at least one member)
genPair :: (1 <= w) => NatRepr w -> Gen (Tnum w, Integer)
genPair w = do
  r <- chooseInteger (0, 9)  -- 0-9 instead of 0-10 to skip bottom
  if r == 0
    then do
      -- Generate top and a random member
      x <- chooseInteger (0, bvdMask w)
      Prelude.pure (top w, x)
    else do
      -- Generate a random non-bottom tnum
      value <- chooseInteger (0, bvdMask w)
      mask <- chooseInteger (0, bvdMask w)
      let validValue = value .&. complement mask
          t = Tnum w validValue mask
          -- Generate member by: value | (random & mask)
      unknownBits <- chooseInteger (0, mask)
      let x = validValue .|. (unknownBits .&. mask)
      Prelude.pure (t, x)

--------------------------------------------------------------------------------
-- Correctness properties

-- | Soundness property: singleton tnum contains the given value
correct_singleton :: (1 <= w) => NatRepr w -> Integer -> Property
correct_singleton w x =
  property $ member (singleton w x) x

-- | Soundness property: membership test is sound
correct_member :: (1 <= w) => (Tnum w, Integer) -> Property
correct_member (t, x) =
  property $ member t x

-- | Soundness property: fromRange contains all values in the range
correct_from_range :: (1 <= w) => NatRepr w -> Integer -> Integer -> Integer -> Property
correct_from_range w lo hi x =
  let mask = bvdMask w
      lo' = lo .&. mask
      hi' = hi .&. mask
      x' = x .&. mask
   in property $ if lo' <= x' && x' <= hi'
                 then member (fromRange w lo' hi') x'
                 else True

-- | Soundness property for join
correct_join :: (1 <= w) => (Tnum w, Integer) -> (Tnum w, Integer) -> Property
correct_join (t1, x) (t2, _y) =
  property $ member (join t1 t2) x

-- | Soundness property for meet
correct_meet :: (1 <= w) => (Tnum w, Integer) -> (Tnum w, Integer) -> Property
correct_meet (t1, x) (t2, y) =
  let m = meet t1 t2
   in property $ if x == y then member m x else True

-- | Soundness property for subsumption
correct_le :: (1 <= w) => (Tnum w, Integer) -> (Tnum w, Integer) -> Property
correct_le (t1, x) (t2, _y) =
  property $ if t1 `le` t2 then member t2 x else True

-- | Soundness property for AND
correct_and :: (1 <= w) => (Tnum w, Integer) -> (Tnum w, Integer) -> Property
correct_and (t1, x) (t2, y) =
  property $ member (t1 `and` t2) (x .&. y)

-- | Soundness property for OR
correct_or :: (1 <= w) => (Tnum w, Integer) -> (Tnum w, Integer) -> Property
correct_or (t1, x) (t2, y) =
  property $ member (t1 `or` t2) (x .|. y)

-- | Soundness property for XOR
correct_xor :: (1 <= w) => (Tnum w, Integer) -> (Tnum w, Integer) -> Property
correct_xor (t1, x) (t2, y) =
  property $ member (t1 `xor` t2) (x `Bits.xor` y)

-- | Soundness property for NOT
correct_not :: (1 <= w) => (Tnum w, Integer) -> Property
correct_not (t, x) =
  let w = width t
      mask = bvdMask w
   in property $ member (not t) ((complement x) .&. mask)

-- | Soundness property for SHL
correct_shl :: (1 <= w) => (Tnum w, Integer) -> Integer -> Property
correct_shl (t, x) k =
  let w = width t
      mask = bvdMask w
      k' = k `mod` fromIntegral (natValue w)
   in property $ member (shl t k') ((x `shiftL` fromIntegral k') .&. mask)

-- | Soundness property for LSHR
correct_lshr :: (1 <= w) => (Tnum w, Integer) -> Integer -> Property
correct_lshr (t, x) k =
  let w = width t
      k' = k `mod` fromIntegral (natValue w)
   in property $ member (lshr t k') (x `shiftR` fromIntegral k')

-- | Soundness property for ASHR
correct_ashr :: (1 <= w) => (Tnum w, Integer) -> Integer -> Property
correct_ashr (t, x) k =
  let w = width t
      widthInt = fromIntegral (natValue w) :: Int
      k' = k `mod` fromIntegral (natValue w)
      -- Compute expected result
      xSigned = if Bits.testBit x (widthInt - 1)
                then x - bit widthInt  -- Convert to signed
                else x
      resultSigned = xSigned `shiftR` fromIntegral k'
      result = resultSigned .&. bvdMask w
   in property $ member (ashr t k') result

-- | Soundness property for addition
correct_add :: (1 <= w) => (Tnum w, Integer) -> (Tnum w, Integer) -> Property
correct_add (t1, x) (t2, y) =
  let w = width t1
      mask = bvdMask w
   in property $ member (add t1 t2) ((x + y) .&. mask)

-- | Soundness property for negation
correct_neg :: (1 <= w) => (Tnum w, Integer) -> Property
correct_neg (t, x) =
  let w = width t
      mask = bvdMask w
   in property $ member (neg t) ((negate x) .&. mask)

-- | Soundness property for subtraction
correct_sub :: (1 <= w) => (Tnum w, Integer) -> (Tnum w, Integer) -> Property
correct_sub (t1, x) (t2, y) =
  let w = width t1
      mask = bvdMask w
   in property $ member (sub t1 t2) ((x - y) .&. mask)

-- | Soundness property for multiplication
correct_mul :: (1 <= w) => (Tnum w, Integer) -> (Tnum w, Integer) -> Property
correct_mul (t1, x) (t2, y) =
  let w = width t1
      mask = bvdMask w
   in property $ member (mul t1 t2) ((x * y) .&. mask)

-- | Soundness property for unsigned division
correct_udiv :: (1 <= w) => (Tnum w, Integer) -> (Tnum w, Integer) -> Property
correct_udiv (t1, x) (t2, y) =
  let w = width t1
      mask = bvdMask w
   in if y == 0
      then property True  -- Skip division by zero
      else property $ member (udiv t1 t2) ((x `div` y) .&. mask)

-- | Soundness property for signed division
correct_sdiv :: (1 <= w) => (Tnum w, Integer) -> (Tnum w, Integer) -> Property
correct_sdiv (t1, x) (t2, y) =
  let w = width t1
      mask = bvdMask w
      widthInt = fromIntegral (natValue w) :: Int
      -- Convert to signed interpretation
      toSigned v = if Bits.testBit v (widthInt - 1)
                   then v - (Bits.bit widthInt)
                   else v
      xs = toSigned x
      ys = toSigned y
   in if ys == 0
      then property True  -- Skip division by zero
      else property $ member (sdiv t1 t2) ((xs `quot` ys) .&. mask)

-- | Soundness property for unsigned remainder
correct_urem :: (1 <= w) => (Tnum w, Integer) -> (Tnum w, Integer) -> Property
correct_urem (t1, x) (t2, y) =
  let w = width t1
      mask = bvdMask w
   in if y == 0
      then property True  -- Skip division by zero
      else property $ member (urem t1 t2) ((x `mod` y) .&. mask)

-- | Soundness property for signed remainder
correct_srem :: (1 <= w) => (Tnum w, Integer) -> (Tnum w, Integer) -> Property
correct_srem (t1, x) (t2, y) =
  let w = width t1
      mask = bvdMask w
      widthInt = fromIntegral (natValue w) :: Int
      -- Convert to signed interpretation
      toSigned v = if Bits.testBit v (widthInt - 1)
                   then v - (Bits.bit widthInt)
                   else v
      xs = toSigned x
      ys = toSigned y
   in if ys == 0
      then property True  -- Skip division by zero
      else property $ member (srem t1 t2) ((xs `rem` ys) .&. mask)

-- | Soundness property for zero extension
correct_zext :: (1 <= w, w+1 <= u) => NatRepr u -> (Tnum w, Integer) -> Property
correct_zext u (t, x) =
  let mask = bvdMask u
   in property $ member (zext t u) (x .&. mask)

-- | Soundness property for sign extension
correct_sext :: (1 <= w, 1 <= u, w+1 <= u) => NatRepr u -> (Tnum w, Integer) -> Property
correct_sext u (t, x) =
  let w = width t
      widthInt = fromIntegral (natValue w) :: Int
      widthU = fromIntegral (natValue u) :: Int
      -- Sign extend x
      signBits = Bits.xor ((Bits.bit widthU :: Integer) - 1) ((Bits.bit widthInt :: Integer) - 1)
      xSigned = if Bits.testBit x (widthInt - 1)
                then (Bits..|.) x signBits
                else x
      mask = bvdMask u
   in property $ member (sext t u) ((Bits..&.) xSigned mask)

-- | Soundness property for truncation
correct_trunc :: (1 <= n, n+1 <= w) => NatRepr n -> (Tnum w, Integer) -> Property
correct_trunc n (t, x) =
  let mask = bvdMask n
   in property $ member (trunc n t) (x .&. mask)

-- | Soundness property for rotate left
correct_rol :: (1 <= w) => (Tnum w, Integer) -> Integer -> Property
correct_rol (t, x) k =
  let w = width t
      widthInt = fromIntegral (natValue w) :: Int
      k' = fromIntegral (k `mod` fromIntegral widthInt) :: Int
      mask = bvdMask w
      rotated = ((x `shiftL` k') .|. (x `shiftR` (widthInt - k'))) .&. mask
   in property $ member (rol t k) rotated

-- | Soundness property for rotate right
correct_ror :: (1 <= w) => (Tnum w, Integer) -> Integer -> Property
correct_ror (t, x) k =
  let w = width t
      widthInt = fromIntegral (natValue w) :: Int
      k' = fromIntegral (k `mod` fromIntegral widthInt) :: Int
      mask = bvdMask w
      rotated = ((x `shiftR` k') .|. (x `shiftL` (widthInt - k'))) .&. mask
   in property $ member (ror t k) rotated

--------------------------------------------------------------------------------
-- Lattice property tests

-- | Join commutativity: join(a, b) = join(b, a)
lattice_join_commutative :: (1 <= w) => Tnum w -> Tnum w -> Property
lattice_join_commutative t1 t2 =
  property $ join t1 t2 == join t2 t1

-- | Meet commutativity: meet(a, b) = meet(b, a)
lattice_meet_commutative :: (1 <= w) => Tnum w -> Tnum w -> Property
lattice_meet_commutative t1 t2 =
  property $ meet t1 t2 == meet t2 t1

-- | Join associativity: join(a, join(b, c)) = join(join(a, b), c)
lattice_join_associative :: (1 <= w) => Tnum w -> Tnum w -> Tnum w -> Property
lattice_join_associative t1 t2 t3 =
  property $ join t1 (join t2 t3) == join (join t1 t2) t3

-- | Meet associativity: meet(a, meet(b, c)) = meet(meet(a, b), c)
lattice_meet_associative :: (1 <= w) => Tnum w -> Tnum w -> Tnum w -> Property
lattice_meet_associative t1 t2 t3 =
  property $ meet t1 (meet t2 t3) == meet (meet t1 t2) t3

-- | Join idempotence: join(a, a) = a
lattice_join_idempotent :: (1 <= w) => Tnum w -> Property
lattice_join_idempotent t =
  property $ join t t == t

-- | Meet idempotence: meet(a, a) = a
lattice_meet_idempotent :: (1 <= w) => Tnum w -> Property
lattice_meet_idempotent t =
  property $ meet t t == t

-- | Absorption law 1: join(a, meet(a, b)) = a
lattice_absorption1 :: (1 <= w) => Tnum w -> Tnum w -> Property
lattice_absorption1 t1 t2 =
  property $ join t1 (meet t1 t2) == t1

-- | Absorption law 2: meet(a, join(a, b)) = a
lattice_absorption2 :: (1 <= w) => Tnum w -> Tnum w -> Property
lattice_absorption2 t1 t2 =
  property $ meet t1 (join t1 t2) == t1

-- | LE reflexivity: a <= a
lattice_le_reflexive :: (1 <= w) => Tnum w -> Property
lattice_le_reflexive t =
  property $ t `le` t

-- | LE antisymmetry: if a <= b and b <= a then a = b
lattice_le_antisymmetric :: (1 <= w) => Tnum w -> Tnum w -> Property
lattice_le_antisymmetric t1 t2 =
  property $ if t1 `le` t2 && t2 `le` t1 then t1 == t2 else True

-- | LE transitivity: if a <= b and b <= c then a <= c
lattice_le_transitive :: (1 <= w) => Tnum w -> Tnum w -> Tnum w -> Property
lattice_le_transitive t1 t2 t3 =
  property $ if t1 `le` t2 && t2 `le` t3 then t1 `le` t3 else True

-- | Join is upper bound: a <= join(a, b)
lattice_join_upper_bound1 :: (1 <= w) => Tnum w -> Tnum w -> Property
lattice_join_upper_bound1 t1 t2 =
  property $ t1 `le` join t1 t2

-- | Join is upper bound: b <= join(a, b)
lattice_join_upper_bound2 :: (1 <= w) => Tnum w -> Tnum w -> Property
lattice_join_upper_bound2 t1 t2 =
  property $ t2 `le` join t1 t2

-- | Meet is lower bound: meet(a, b) <= a
lattice_meet_lower_bound1 :: (1 <= w) => Tnum w -> Tnum w -> Property
lattice_meet_lower_bound1 t1 t2 =
  property $ meet t1 t2 `le` t1

-- | Meet is lower bound: meet(a, b) <= b
lattice_meet_lower_bound2 :: (1 <= w) => Tnum w -> Tnum w -> Property
lattice_meet_lower_bound2 t1 t2 =
  property $ meet t1 t2 `le` t2

-- | Join is least upper bound: if a <= c and b <= c then join(a,b) <= c
lattice_join_least_upper_bound :: (1 <= w) => Tnum w -> Tnum w -> Tnum w -> Property
lattice_join_least_upper_bound t1 t2 t3 =
  property $ if t1 `le` t3 && t2 `le` t3 then join t1 t2 `le` t3 else True

-- | Meet is greatest lower bound: if c <= a and c <= b then c <= meet(a,b)
lattice_meet_greatest_lower_bound :: (1 <= w) => Tnum w -> Tnum w -> Tnum w -> Property
lattice_meet_greatest_lower_bound t1 t2 t3 =
  property $ if t3 `le` t1 && t3 `le` t2 then t3 `le` meet t1 t2 else True

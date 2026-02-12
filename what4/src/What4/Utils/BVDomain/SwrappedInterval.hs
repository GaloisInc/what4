{-|
Module      : What4.Utils.BVDomain.SwrappedInterval
Copyright   : (c) Galois Inc, 2025
License     : BSD3
Maintainer  : langston@galois.com

Provides swrapped_interval (hemisphere-based interval) abstract domain for bitvectors.

A SwrappedInterval represents sets of bitvectors using two intervals per value,
one for each hemisphere:
- Hemisphere 0: MSB=0 (non-negative: 0 to 2^(w-1)-1)
- Hemisphere 1: MSB=1 (negative: 2^(w-1) to 2^w-1)

This enables precise tracking of values that cross the sign bit boundary, providing
better precision than traditional wrapped intervals for cross-sign ranges.

Based on algorithms from:
- Clam static analyzer (crab/domains/swrapped_interval_impl.hpp)
- "Signedness-Agnostic Program Analysis" (ISSTA 2025)
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module What4.Utils.BVDomain.SwrappedInterval
  ( -- * SwrappedInterval type
    SwrappedInterval(..)
  , bottom, top, singleton, fromRange
  , isBottom, isTop, member, proper, asSingleton
    -- * The critical split function
  , split
    -- * Lattice operations
  , join, meet, le
    -- * Arithmetic operations
  , add, neg, sub, mul
  , udiv, sdiv, urem, srem
    -- * Bitwise operations
  , and, or, xor, not
    -- * Shift operations
  , shl, lshr, ashr
    -- * Width operations
  , zext, sext, trunc
  , rol, ror
    -- * Bounds extraction
  , getSignedMin, getSignedMax
  , getUnsignedMin, getUnsignedMax
    -- * Transfer functions
  , transferUlt, transferSlt
  , lowerHalfLine, upperHalfLine
    -- * Testing support
  , genSwrappedInterval, genSwrappedIntervalPair
    -- * Correctness properties
  , correct_singleton
  , correct_member
  , correct_split
  , correct_from_range
  , correct_join
  , correct_meet
  , correct_le
  , correct_add
  , correct_neg
  , correct_sub
  , correct_mul
  , correct_udiv
  , correct_sdiv
  , correct_urem
  , correct_srem
  , correct_and
  , correct_or
  , correct_xor
  , correct_not
  , correct_shl
  , correct_lshr
  , correct_ashr
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

import           Test.Verification ( Gen, chooseInteger, Property, property, (==>) )

--------------------------------------------------------------------------------
-- SwrappedInterval definition

-- | A SwrappedInterval represents a set of bitvectors using two intervals,
-- one per hemisphere (based on MSB).
--
-- Representation invariants:
-- 1. Hemisphere bounds: 0 ≤ swStart0, swEnd0 < 2^(w-1) and 2^(w-1) ≤ swStart1, swEnd1 < 2^w
-- 2. Non-wrapped: If not bottom, then swStart0 ≤ swEnd0 and swStart1 ≤ swEnd1
-- 3. Bottom: bottom0 = True AND bottom1 = True
--
-- Each hemisphere represents a contiguous range [start, end].
data SwrappedInterval (w :: Nat) = SwrappedInterval
  { -- Hemisphere 0: MSB=0 (non-negative: 0 to 2^(w-1)-1)
    swStart0    :: !Integer
  , swEnd0      :: !Integer
  , bottom0   :: !Bool

    -- Hemisphere 1: MSB=1 (negative: 2^(w-1) to 2^w-1)
  , swStart1    :: !Integer
  , swEnd1      :: !Integer
  , bottom1   :: !Bool

    -- Width witness
  , swWidth     :: !(NatRepr w)
  }

deriving instance Show (SwrappedInterval w)

-- | Equality for SwrappedIntervals
instance Eq (SwrappedInterval w) where
  sw1 == sw2 =
    -- Compare hemisphere 0 (ignore start/end if bottom)
    (bottom0 sw1 && bottom0 sw2 ||
     (Prelude.not (bottom0 sw1) && Prelude.not (bottom0 sw2) &&
      swStart0 sw1 == swStart0 sw2 && swEnd0 sw1 == swEnd0 sw2)) &&
    -- Compare hemisphere 1 (ignore start/end if bottom)
    (bottom1 sw1 && bottom1 sw2 ||
     (Prelude.not (bottom1 sw1) && Prelude.not (bottom1 sw2) &&
      swStart1 sw1 == swStart1 sw2 && swEnd1 sw1 == swEnd1 sw2))

--------------------------------------------------------------------------------
-- Basic constructors and queries

-- | Get the bitvector width
swGetWidth :: SwrappedInterval w -> NatRepr w
swGetWidth = swWidth

-- | Maximum unsigned value for width w: 2^w - 1
swMaxUnsigned :: NatRepr w -> Integer
swMaxUnsigned w = bit (fromIntegral (natValue w)) - 1

-- | Half range for width w: 2^(w-1)
halfRange :: NatRepr w -> Integer
halfRange w = bit (fromIntegral (natValue w) - 1)

-- | Bottom element (empty set)
bottom :: (1 <= w) => NatRepr w -> SwrappedInterval w
bottom w = SwrappedInterval 0 0 True 0 0 True w

-- | Top element (all values)
top :: (1 <= w) => NatRepr w -> SwrappedInterval w
top w =
  let half = halfRange w
      maxVal = swMaxUnsigned w
   in SwrappedInterval 0 (half - 1) False half maxVal False w

-- | Singleton interval representing exactly one value
singleton :: (1 <= w) => NatRepr w -> Integer -> SwrappedInterval w
singleton w x =
  let widthInt = fromIntegral (natValue w) :: Int
      half = halfRange w
      maxVal = swMaxUnsigned w
      x' = x .&. maxVal
      msb = Bits.testBit x' (widthInt - 1)
   in if msb
      then SwrappedInterval (half - 1) 0 True x' x' False w
      else SwrappedInterval x' x' False half maxVal True w

-- | Check if SwrappedInterval is bottom (empty set)
isBottom :: SwrappedInterval w -> Bool
isBottom sw = bottom0 sw && bottom1 sw

-- | Check if SwrappedInterval is top (all values)
isTop :: SwrappedInterval w -> Bool
isTop sw =
  let w = swWidth sw
      half = halfRange w
      maxVal = swMaxUnsigned w
   in Prelude.not (isBottom sw) &&
      Prelude.not (bottom0 sw) && swStart0 sw == 0 && swEnd0 sw == (half - 1) &&
      Prelude.not (bottom1 sw) && swStart1 sw == half && swEnd1 sw == maxVal

-- | Check if a value is a member of the SwrappedInterval
member :: SwrappedInterval w -> Integer -> Bool
member sw x
  | isBottom sw = False
  | otherwise =
      let w = swWidth sw
          widthInt = fromIntegral (natValue w) :: Int
          maxVal = swMaxUnsigned w
          x' = x .&. maxVal
          msb = Bits.testBit x' (widthInt - 1)
       in if msb
          then Prelude.not (bottom1 sw) && swStart1 sw <= x' && x' <= swEnd1 sw
          else Prelude.not (bottom0 sw) && swStart0 sw <= x' && x' <= swEnd0 sw

-- | Check if SwrappedInterval satisfies representation invariants
proper :: SwrappedInterval w -> Bool
proper sw =
  let w = swWidth sw
      widthInt = fromIntegral (natValue w) :: Int
      half = halfRange w
      maxVal = swMaxUnsigned w
      -- Bottom check
      bothBottom = bottom0 sw && bottom1 sw
      -- Hemisphere 0 bounds
      h0BoundsOk = swStart0 sw >= 0 && swStart0 sw < half &&
                   swEnd0 sw >= 0 && swEnd0 sw < half
      h0OrderOk = bottom0 sw || swStart0 sw <= swEnd0 sw
      -- Hemisphere 1 bounds
      h1BoundsOk = swStart1 sw >= half && swStart1 sw <= maxVal &&
                   swEnd1 sw >= half && swEnd1 sw <= maxVal
      h1OrderOk = bottom1 sw || swStart1 sw <= swEnd1 sw
   in if bothBottom
      then True  -- Bottom is valid
      else h0BoundsOk && h0OrderOk && h1BoundsOk && h1OrderOk

-- | Return value if this is a singleton
asSingleton :: SwrappedInterval w -> Maybe Integer
asSingleton sw
  | isBottom sw = Nothing
  | bottom0 sw && Prelude.not (bottom1 sw) && swStart1 sw == swEnd1 sw =
      Just (swStart1 sw)
  | Prelude.not (bottom0 sw) && bottom1 sw && swStart0 sw == swEnd0 sw =
      Just (swStart0 sw)
  | otherwise = Nothing

--------------------------------------------------------------------------------
-- The critical split function

-- | Split a traditional wrapped interval [start, end] into hemisphere representation.
--
-- This is the most important function in the module - it converts traditional
-- wrapped intervals to the dual-hemisphere representation.
--
-- Algorithm from Clam swrapped_interval_impl.hpp:43-69
split :: (1 <= w) => NatRepr w -> Integer -> Integer -> SwrappedInterval w
split w start end =
  let widthInt = fromIntegral (natValue w) :: Int
      maxVal = swMaxUnsigned w
      half = halfRange w
      start' = start .&. maxVal
      end' = end .&. maxVal
      startMsb = Bits.testBit start' (widthInt - 1)
      endMsb = Bits.testBit end' (widthInt - 1)
   in if Prelude.not startMsb && Prelude.not endMsb
      then -- Both in hemisphere 0
        if start' <= end'
        then SwrappedInterval start' end' False maxVal half True w
        else top w  -- Wrapped around
      else if Prelude.not startMsb && endMsb
      then -- Crosses from hemi0 to hemi1
        SwrappedInterval start' (half - 1) False half end' False w
      else if startMsb && Prelude.not endMsb
      then -- Wraps around 2^w
        SwrappedInterval 0 end' False start' maxVal False w
      else -- Both in hemisphere 1
        if start' <= end'
        then SwrappedInterval (half - 1) 0 True start' end' False w
        else top w  -- Wrapped around

-- | Construct SwrappedInterval from unsigned range [lo, hi]
fromRange :: (1 <= w) => NatRepr w -> Integer -> Integer -> SwrappedInterval w
fromRange w lo hi =
  let maxVal = swMaxUnsigned w
      lo' = lo .&. maxVal
      hi' = hi .&. maxVal
   in split w lo' hi'

--------------------------------------------------------------------------------
-- Lattice operations

-- | Lattice join (union) for SwrappedIntervals.
--
-- Join each hemisphere independently.
join :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> SwrappedInterval w
join sw1 sw2
  | isBottom sw1 = sw2
  | isBottom sw2 = sw1
  | otherwise =
      let w = swWidth sw1
          -- Join hemisphere 0
          (h0Start, h0End, h0Bottom) =
            if bottom0 sw1
            then (swStart0 sw2, swEnd0 sw2, bottom0 sw2)
            else if bottom0 sw2
            then (swStart0 sw1, swEnd0 sw1, bottom0 sw1)
            else (min (swStart0 sw1) (swStart0 sw2),
                  max (swEnd0 sw1) (swEnd0 sw2),
                  False)
          -- Join hemisphere 1
          (h1Start, h1End, h1Bottom) =
            if bottom1 sw1
            then (swStart1 sw2, swEnd1 sw2, bottom1 sw2)
            else if bottom1 sw2
            then (swStart1 sw1, swEnd1 sw1, bottom1 sw1)
            else (min (swStart1 sw1) (swStart1 sw2),
                  max (swEnd1 sw1) (swEnd1 sw2),
                  False)
       in SwrappedInterval h0Start h0End h0Bottom h1Start h1End h1Bottom w

-- | Lattice meet (intersection) for SwrappedIntervals.
--
-- Meet each hemisphere independently.
meet :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> SwrappedInterval w
meet sw1 sw2
  | isBottom sw1 = sw1
  | isBottom sw2 = sw2
  | otherwise =
      let w = swWidth sw1
          -- Meet hemisphere 0
          (h0Start, h0End, h0Bottom) =
            if bottom0 sw1 || bottom0 sw2
            then (0, 0, True)
            else let newStart = max (swStart0 sw1) (swStart0 sw2)
                     newEnd = min (swEnd0 sw1) (swEnd0 sw2)
                  in if newStart <= newEnd
                     then (newStart, newEnd, False)
                     else (0, 0, True)  -- Empty intersection
          -- Meet hemisphere 1
          (h1Start, h1End, h1Bottom) =
            if bottom1 sw1 || bottom1 sw2
            then (0, 0, True)
            else let newStart = max (swStart1 sw1) (swStart1 sw2)
                     newEnd = min (swEnd1 sw1) (swEnd1 sw2)
                  in if newStart <= newEnd
                     then (newStart, newEnd, False)
                     else (0, 0, True)  -- Empty intersection
       in -- Return canonical bottom if both hemispheres are empty
          if h0Bottom && h1Bottom
          then bottom w
          else SwrappedInterval h0Start h0End h0Bottom h1Start h1End h1Bottom w

-- | Remove zero from interval (for division operations)
-- If the interval contains 0, adjust it to start from 1
trimZero :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w
trimZero sw
  | isBottom sw = sw
  | singleton (swWidth sw) 0 `le` sw && sw `le` singleton (swWidth sw) 0 = bottom (swWidth sw)  -- Interval is exactly {0}
  | bottom0 sw = sw  -- Hemisphere 0 is empty, 0 not present
  | swStart0 sw == 0 =
      -- Hemisphere 0 starts at 0, adjust to start at 1
      if swEnd0 sw == 0
      then SwrappedInterval 0 0 True (swStart1 sw) (swEnd1 sw) (bottom1 sw) (swWidth sw)
      else SwrappedInterval 1 (swEnd0 sw) False (swStart1 sw) (swEnd1 sw) (bottom1 sw) (swWidth sw)
  | otherwise = sw

-- | Subsumption test: sw1 `le` sw2 iff sw1 represents a subset of sw2
le :: SwrappedInterval w -> SwrappedInterval w -> Bool
le sw1 sw2
  | isBottom sw1 = True
  | isBottom sw2 = False
  | otherwise =
      let -- Hemisphere 0 subsumption
          h0Ok = bottom0 sw1 ||
                 (Prelude.not (bottom0 sw2) &&
                  swStart0 sw2 <= swStart0 sw1 &&
                  swEnd0 sw1 <= swEnd0 sw2)
          -- Hemisphere 1 subsumption
          h1Ok = bottom1 sw1 ||
                 (Prelude.not (bottom1 sw2) &&
                  swStart1 sw2 <= swStart1 sw1 &&
                  swEnd1 sw1 <= swEnd1 sw2)
       in h0Ok && h1Ok

--------------------------------------------------------------------------------
-- Arithmetic operations

-- | Join all intervals in a list (helper for 2x2 matrix pattern)
joinAll :: (1 <= w) => [SwrappedInterval w] -> SwrappedInterval w
joinAll [] = error "joinAll: empty list"
joinAll (sw:sws) = foldl join sw sws

-- | Addition with 2x2 matrix pattern
add :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> SwrappedInterval w
add sw1 sw2
  | isBottom sw1 || isBottom sw2 = bottom (swWidth sw1)
  | otherwise =
      let w = swWidth sw1
          maxVal = swMaxUnsigned w
          -- Extract intervals
          results = []
          -- hemi0 + hemi0
          results1 = if bottom0 sw1 || bottom0 sw2
                     then results
                     else split w (swStart0 sw1 + swStart0 sw2) (swEnd0 sw1 + swEnd0 sw2) : results
          -- hemi0 + hemi1
          results2 = if bottom0 sw1 || bottom1 sw2
                     then results1
                     else split w (swStart0 sw1 + swStart1 sw2) (swEnd0 sw1 + swEnd1 sw2) : results1
          -- hemi1 + hemi0
          results3 = if bottom1 sw1 || bottom0 sw2
                     then results2
                     else split w (swStart1 sw1 + swStart0 sw2) (swEnd1 sw1 + swEnd0 sw2) : results2
          -- hemi1 + hemi1
          results4 = if bottom1 sw1 || bottom1 sw2
                     then results3
                     else split w (swStart1 sw1 + swStart1 sw2) (swEnd1 sw1 + swEnd1 sw2) : results3
       in if null results4
          then bottom w
          else joinAll results4

-- | Negation (two's complement)
--
-- Negation flips hemispheres and reverses intervals.
neg :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w
neg sw
  | isBottom sw = sw
  | otherwise =
      let w = swWidth sw
          maxVal = swMaxUnsigned w
          -- Compute the negated ranges
          neg0 = if bottom0 sw
                 then bottom w
                 else let negEnd = (Prelude.negate (swStart0 sw)) .&. maxVal
                          negStart = (Prelude.negate (swEnd0 sw)) .&. maxVal
                       in split w negStart negEnd
          neg1 = if bottom1 sw
                 then bottom w
                 else let negEnd = (Prelude.negate (swStart1 sw)) .&. maxVal
                          negStart = (Prelude.negate (swEnd1 sw)) .&. maxVal
                       in split w negStart negEnd
       in join neg0 neg1

-- | Subtraction: x - y = x + (-y)
sub :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> SwrappedInterval w
sub sw1 sw2 = add sw1 (neg sw2)

-- | Helper: compute unsigned multiplication checking for wrapping
unsignedMulRange :: Integer -> Integer -> Integer -> Integer -> Integer -> (Integer, Integer, Bool)
unsignedMulRange start1 end1 start2 end2 maxVal =
  let lo = start1 * start2
      hi = end1 * end2
      -- Check if result wraps: (a * b) > 2^w - 1
      wraps = hi > maxVal
   in (lo .&. maxVal, hi .&. maxVal, wraps)

-- | Unsigned multiplication for a single pair of ranges
unsignedMul :: (1 <= w) => NatRepr w -> Integer -> Integer -> Integer -> Integer -> SwrappedInterval w
unsignedMul w start1 end1 start2 end2 =
  let maxVal = swMaxUnsigned w
      (lo, hi, wraps) = unsignedMulRange start1 end1 start2 end2 maxVal
   in if wraps
      then top w  -- Conservative: wrapping detected
      else split w lo hi

-- | Signed multiplication for a single pair of ranges
signedMul :: (1 <= w) => NatRepr w -> Integer -> Integer -> Integer -> Integer -> SwrappedInterval w
signedMul w start1 end1 start2 end2 =
  let widthInt = fromIntegral (natValue w) :: Int
      maxVal = swMaxUnsigned w
      msb1Start = Bits.testBit start1 (widthInt - 1)
      msb1End = Bits.testBit end1 (widthInt - 1)
      msb2Start = Bits.testBit start2 (widthInt - 1)
      msb2End = Bits.testBit end2 (widthInt - 1)
      -- Check if both operands are in same hemisphere
      sameHemi1 = msb1Start == msb1End
      sameHemi2 = msb2Start == msb2End
   in if sameHemi1 && sameHemi2
      then -- Both ranges in same hemisphere each
        if Prelude.not msb1Start && Prelude.not msb2Start
        then -- Both non-negative: use unsigned multiplication
          unsignedMul w start1 end1 start2 end2
        else if msb1Start && msb2Start
        then -- Both negative: result is positive, endpoints reversed
          let (lo, hi, wraps) = unsignedMulRange end1 start1 end2 start2 maxVal
           in if wraps
              then top w
              else split w (end1 * end2) (start1 * start2)
        else top w  -- Mixed hemispheres
      else top w  -- At least one range crosses hemispheres

-- | Multiplication with reduced product
--
-- Compute both signed and unsigned multiplication, then meet the results.
mul :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> SwrappedInterval w
mul sw1 sw2
  | isBottom sw1 || isBottom sw2 = bottom (swWidth sw1)
  | otherwise =
      let w = swWidth sw1
          -- Compute all 4 combinations for unsigned multiplication
          unsignedResults = []
          ur1 = if bottom0 sw1 || bottom0 sw2
                then unsignedResults
                else unsignedMul w (swStart0 sw1) (swEnd0 sw1) (swStart0 sw2) (swEnd0 sw2) : unsignedResults
          ur2 = if bottom0 sw1 || bottom1 sw2
                then ur1
                else unsignedMul w (swStart0 sw1) (swEnd0 sw1) (swStart1 sw2) (swEnd1 sw2) : ur1
          ur3 = if bottom1 sw1 || bottom0 sw2
                then ur2
                else unsignedMul w (swStart1 sw1) (swEnd1 sw1) (swStart0 sw2) (swEnd0 sw2) : ur2
          ur4 = if bottom1 sw1 || bottom1 sw2
                then ur3
                else unsignedMul w (swStart1 sw1) (swEnd1 sw1) (swStart1 sw2) (swEnd1 sw2) : ur3
          unsignedResult = if null ur4 then bottom w else joinAll ur4

          -- Compute all 4 combinations for signed multiplication
          signedResults = []
          sr1 = if bottom0 sw1 || bottom0 sw2
                then signedResults
                else signedMul w (swStart0 sw1) (swEnd0 sw1) (swStart0 sw2) (swEnd0 sw2) : signedResults
          sr2 = if bottom0 sw1 || bottom1 sw2
                then sr1
                else signedMul w (swStart0 sw1) (swEnd0 sw1) (swStart1 sw2) (swEnd1 sw2) : sr1
          sr3 = if bottom1 sw1 || bottom0 sw2
                then sr2
                else signedMul w (swStart1 sw1) (swEnd1 sw1) (swStart0 sw2) (swEnd0 sw2) : sr2
          sr4 = if bottom1 sw1 || bottom1 sw2
                then sr3
                else signedMul w (swStart1 sw1) (swEnd1 sw1) (swStart1 sw2) (swEnd1 sw2) : sr3
          signedResult = if null sr4 then bottom w else joinAll sr4

       in meet unsignedResult signedResult  -- Reduced product

-- | Unsigned division
udiv :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> SwrappedInterval w
udiv sw1 sw2
  | isBottom sw1 || isBottom sw2 = bottom (swWidth sw1)
  | isTop sw1 || isTop sw2 = top (swWidth sw1)
  | otherwise =
      let sw2' = trimZero sw2
       in if isBottom sw2' then bottom (swWidth sw1) else unsignedDiv sw1 sw2'
  where
    unsignedDiv sw1 sw2 =
      let w = swWidth sw1
          half = halfRange w
          maxVal = swMaxUnsigned w
          -- h0 / h0: small / small = small (in h0)
          res00 = if bottom0 sw1 || bottom0 sw2
                  then bottom w
                  else SwrappedInterval
                       (swStart0 sw1 `div` swEnd0 sw2)
                       (swEnd0 sw1 `div` swStart0 sw2)
                       False
                       maxVal half True w
          -- h0 / h1: small / large = 0
          res01 = if bottom0 sw1 || bottom1 sw2
                  then bottom w
                  else singleton w 0
          -- h1 / h0: large / small = result is in [start1/end0, end1/start0]
          res10 = if bottom1 sw1 || bottom0 sw2
                  then bottom w
                  else split w (swStart1 sw1 `div` swEnd0 sw2) (swEnd1 sw1 `div` swStart0 sw2)
          -- h1 / h1: large / large = could be anything
          res11 = if bottom1 sw1 || bottom1 sw2
                  then bottom w
                  else split w (swStart1 sw1 `div` swEnd1 sw2) (swEnd1 sw1 `div` swStart1 sw2)
       in joinAll [res00, res01, res10, res11]

-- | Convert to signed interpretation
swToSigned :: NatRepr w -> Integer -> Integer
swToSigned w x =
  let widthInt = fromIntegral (natValue w) :: Int
      maxVal = swMaxUnsigned w
      x' = x .&. maxVal
   in if Bits.testBit x' (widthInt - 1)
      then x' - bit widthInt
      else x'

-- | Signed division
sdiv :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> SwrappedInterval w
sdiv sw1 sw2
  | isBottom sw1 || isBottom sw2 = bottom (swWidth sw1)
  | isTop sw1 || isTop sw2 = top (swWidth sw1)
  | otherwise =
      let sw2' = trimZero sw2
       in if isBottom sw2' then bottom (swWidth sw1) else signedDiv sw1 sw2'
  where
    signedDiv sw1 sw2 =
      let w = swWidth sw1
          half = halfRange w
          maxVal = swMaxUnsigned w
          signedMin = half
          signedMax = half - 1
          minusOne = maxVal
          -- Helper for signed division
          sdivSigned x y = swToSigned w x `quot` swToSigned w y
          -- h0 / h0: pos / pos = pos (in h0)
          res00 = if bottom0 sw1 || bottom0 sw2
                  then bottom w
                  else SwrappedInterval
                       (sdivSigned (swStart0 sw1) (swEnd0 sw2))
                       (sdivSigned (swEnd0 sw1) (swStart0 sw2))
                       False
                       maxVal half True w
          -- h0 / h1: pos / neg = neg
          res01 = if bottom0 sw1 || bottom1 sw2
                  then bottom w
                  else split w (sdivSigned (swEnd0 sw1) (swEnd1 sw2))
                               (sdivSigned (swStart0 sw1) (swStart1 sw2))
          -- h1 / h0: neg / pos = neg
          res10 = if bottom1 sw1 || bottom0 sw2
                  then bottom w
                  else split w (sdivSigned (swStart1 sw1) (swStart0 sw2))
                               (sdivSigned (swEnd1 sw1) (swEnd0 sw2))
          -- h1 / h1: neg / neg = pos (but check for overflow)
          res11 = if bottom1 sw1 || bottom1 sw2
                  then bottom w
                  else if (swEnd1 sw1 == signedMin && swStart1 sw2 == minusOne) ||
                          (swStart1 sw1 == signedMin && swEnd1 sw2 == minusOne)
                       -- Overflow case: -2^(w-1) / -1 = 2^(w-1) which overflows
                       then top w
                       else SwrappedInterval
                            (sdivSigned (swEnd1 sw1) (swStart1 sw2))
                            (sdivSigned (swStart1 sw1) (swEnd1 sw2))
                            False
                            maxVal half True w
       in joinAll [res00, res01, res10, res11]

-- | Unsigned remainder
urem :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> SwrappedInterval w
urem sw1 sw2
  | isBottom sw1 || isBottom sw2 = bottom (swWidth sw1)
  | isTop sw1 || isTop sw2 = top (swWidth sw1)
  | otherwise =
      let sw2' = trimZero sw2
       in if isBottom sw2' then bottom (swWidth sw1)
          else let w = swWidth sw1
                   -- Result is in [0, max(sw2') - 1]
                   -- Get the unsigned max value from sw2'
                   maxDivisor = case getUnsignedMax sw2' of
                                  Nothing -> swMaxUnsigned w
                                  Just m -> m
                in split w 0 (maxDivisor - 1)

-- | Signed remainder
srem :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> SwrappedInterval w
srem sw1 sw2
  | isBottom sw1 || isBottom sw2 = bottom (swWidth sw1)
  | isTop sw1 || isTop sw2 = top (swWidth sw1)
  | otherwise =
      let sw2' = trimZero sw2
       in if isBottom sw2' then bottom (swWidth sw1)
          else signedRem sw1 sw2'
  where
    signedRem sw1 sw2 =
      let w = swWidth sw1
          half = halfRange w
          maxVal = swMaxUnsigned w
          divRes = sdiv sw1 sw2
       in -- If division result is singleton, compute exactly
          case asSingleton divRes of
            Just d -> sub sw1 (mul divRes sw2)
            Nothing ->
              -- Conservative approximation
              let -- Get maximum absolute value of divisor
                  getMaxAbs = if bottom0 sw2 && Prelude.not (bottom1 sw2)
                              -- Only h1: max is -start1
                              then Prelude.negate (swToSigned w (swStart1 sw2))
                              else if Prelude.not (bottom0 sw2) && bottom1 sw2
                              -- Only h0: max is end0
                              then swEnd0 sw2
                              else
                              -- Both: max of end0 and -start1
                              max (swEnd0 sw2) (Prelude.negate (swToSigned w (swStart1 sw2)))
                  -- Result range is [0, maxAbs] in h0
                  tmpRes = SwrappedInterval 0 getMaxAbs False maxVal half True w
               in -- Apply sign based on dividend
                  if bottom0 sw1 && Prelude.not (bottom1 sw1)
                  then neg tmpRes  -- Only negative dividend
                  else if Prelude.not (bottom0 sw1) && bottom1 sw1
                  then tmpRes  -- Only positive dividend
                  else join tmpRes (neg tmpRes)  -- Both

--------------------------------------------------------------------------------
-- Bitwise operations
--
-- Note: These operations are intentionally conservative, matching the Clam
-- reference implementation (swrapped_interval_impl.hpp:1893-1907).
-- The reference also returns top for bitwise operations on wrapped intervals.
--
-- Rationale: Bitwise operations on intervals that wrap around are inherently
-- imprecise because:
-- 1. The two-circle representation doesn't align with bit patterns
-- 2. Computing tight bounds would require enumerating all possible values
-- 3. More precise abstractions exist (Tnum, Stnum) for bit-level reasoning

-- | Bitwise AND (conservative).
--
-- Returns top unless bottom. Matches Clam swrapped_interval_impl.hpp:1893.
and :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> SwrappedInterval w
and sw1 sw2
  | isBottom sw1 || isBottom sw2 = bottom (swWidth sw1)
  | otherwise = top (swWidth sw1)

-- | Bitwise OR (conservative).
--
-- Returns top unless bottom. Matches Clam swrapped_interval_impl.hpp:1899.
or :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> SwrappedInterval w
or sw1 sw2
  | isBottom sw1 || isBottom sw2 = bottom (swWidth sw1)
  | otherwise = top (swWidth sw1)

-- | Bitwise XOR (conservative).
--
-- Returns top unless bottom. Matches Clam swrapped_interval_impl.hpp:1905.
xor :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> SwrappedInterval w
xor sw1 sw2
  | isBottom sw1 || isBottom sw2 = bottom (swWidth sw1)
  | otherwise = top (swWidth sw1)

-- | Bitwise NOT
not :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w
not sw
  | isBottom sw = sw
  | otherwise =
      let w = swWidth sw
          maxVal = swMaxUnsigned w
          -- NOT flips the MSB, so hemispheres swap
          -- Hemisphere 0 becomes hemisphere 1: [~end0, ~start0]
          (h1Start', h1End', h1Bottom') =
            if bottom0 sw
            then (halfRange w, halfRange w, True)
            else let notEnd = (complement (swStart0 sw)) .&. maxVal
                     notStart = (complement (swEnd0 sw)) .&. maxVal
                  in (notStart, notEnd, False)
          -- Hemisphere 1 becomes hemisphere 0: [~end1, ~start1]
          (h0Start', h0End', h0Bottom') =
            if bottom1 sw
            then (0, 0, True)
            else let notEnd = (complement (swStart1 sw)) .&. maxVal
                     notStart = (complement (swEnd1 sw)) .&. maxVal
                  in (notStart, notEnd, False)
       in SwrappedInterval h0Start' h0End' h0Bottom' h1Start' h1End' h1Bottom' w

--------------------------------------------------------------------------------
-- Shift operations

-- | Left shift
shl :: (1 <= w) => SwrappedInterval w -> Integer -> SwrappedInterval w
shl sw k
  | isBottom sw = sw
  | isTop sw = sw
  | k <= 0 = sw
  | otherwise =
      let w = swWidth sw
          widthInt = fromIntegral (natValue w) :: Int
          k' = fromIntegral (min k (fromIntegral widthInt))
          half = halfRange w
          maxVal = swMaxUnsigned w
          -- Compute mask: ~((1 << k) - 1) & maxVal
          -- up = 1 << k, then up = up - 1, then up = ~up
          up = (complement (bit k' - 1)) .&. maxVal
       in -- Return conservative approximation: h0 is full, h1 up to 'up'
          SwrappedInterval 0 (half - 1) False half up False w

-- | Logical right shift
lshr :: (1 <= w) => SwrappedInterval w -> Integer -> SwrappedInterval w
lshr sw k
  | isBottom sw = sw
  | isTop sw = sw
  | k <= 0 = sw
  | otherwise =
      let w = swWidth sw
          widthInt = fromIntegral (natValue w) :: Int
          k' = fromIntegral (min k (fromIntegral widthInt))
          half = halfRange w
          maxVal = swMaxUnsigned w
          h0Bot = bottom0 sw
          h1Bot = bottom1 sw
       in if Prelude.not h0Bot && Prelude.not h1Bot
          then -- Both hemispheres: result spans [start0 >> k, end1 >> k]
               SwrappedInterval (swStart0 sw `shiftR` k') (swEnd1 sw `shiftR` k') False
                                maxVal half True w
          else if Prelude.not h0Bot && h1Bot
          then -- Only h0: result is [start0 >> k, end0 >> k]
               SwrappedInterval (swStart0 sw `shiftR` k') (swEnd0 sw `shiftR` k') False
                                maxVal half True w
          else if h0Bot && Prelude.not h1Bot
          then -- Only h1: shift and check if result wraps
               let startShifted = swStart1 sw `shiftR` k'
                   endShifted = swEnd1 sw `shiftR` k'
                in if Bits.testBit startShifted (widthInt - 1)
                   then top w  -- Wrapped, return top
                   else SwrappedInterval startShifted endShifted False
                                         maxVal half True w
          else sw  -- Both bottom, shouldn't happen

-- | Arithmetic right shift
ashr :: (1 <= w) => SwrappedInterval w -> Integer -> SwrappedInterval w
ashr sw k
  | isBottom sw = sw
  | isTop sw = sw
  | k <= 0 = sw
  | otherwise =
      let w = swWidth sw
          widthInt = fromIntegral (natValue w) :: Int
          maxVal = swMaxUnsigned w
          k' = fromIntegral (min k (fromIntegral widthInt))
          half = halfRange w
          h0Bot = bottom0 sw
          h1Bot = bottom1 sw
          -- Arithmetic shift helper
          ashrOp x = let signExt = if Bits.testBit x (widthInt - 1)
                                   then (maxVal `shiftL` (widthInt - k')) .&. maxVal
                                   else 0
                      in (x `shiftR` k') .|. signExt
       in if Prelude.not h0Bot && Prelude.not h1Bot
          then -- Both hemispheres
               SwrappedInterval (ashrOp (swStart0 sw)) (ashrOp (swEnd0 sw)) False
                                (ashrOp (swStart1 sw)) (ashrOp (swEnd1 sw)) False w
          else if Prelude.not h0Bot && h1Bot
          then -- Only h0
               SwrappedInterval (ashrOp (swStart0 sw)) (ashrOp (swEnd0 sw)) False
                                half maxVal True w
          else if h0Bot && Prelude.not h1Bot
          then -- Only h1
               SwrappedInterval (half - 1) 0 True
                                (ashrOp (swStart1 sw)) (ashrOp (swEnd1 sw)) False w
          else sw  -- Both bottom

--------------------------------------------------------------------------------
-- Width operations

-- | Zero extension
zext :: (1 <= w, 1 <= u, w+1 <= u) => SwrappedInterval w -> NatRepr u -> SwrappedInterval u
zext sw u
  | isBottom sw = bottom u
  | otherwise =
      -- Hemisphere 0 stays in hemisphere 0
      -- Hemisphere 1 may move to hemisphere 0 (MSB becomes 0 after extension)
      let h0 = if bottom0 sw
               then bottom u
               else fromRange u (swStart0 sw) (swEnd0 sw)
          h1Ext = if bottom1 sw
                  then bottom u
                  else fromRange u (swStart1 sw) (swEnd1 sw)
       in join h0 h1Ext

-- | Sign extension
sext :: (1 <= w, 1 <= u, w+1 <= u) => SwrappedInterval w -> NatRepr u -> SwrappedInterval u
sext sw u
  | isBottom sw = bottom u
  | otherwise =
      let widthInt = fromIntegral (natValue (swWidth sw)) :: Int
          newWidthInt = fromIntegral (natValue u) :: Int
          extBits = newWidthInt - widthInt
          -- Hemisphere 0 (non-negative): zero extend
          h0 = if bottom0 sw
               then bottom u
               else fromRange u (swStart0 sw) (swEnd0 sw)
          -- Hemisphere 1 (negative): sign extend
          h1 = if bottom1 sw
               then bottom u
               else let signExtMask = ((bit extBits - 1) `shiftL` widthInt)
                        newStart = swStart1 sw .|. signExtMask
                        newEnd = swEnd1 sw .|. signExtMask
                     in fromRange u newStart newEnd
       in join h0 h1

-- | Truncation
trunc :: (1 <= n, n+1 <= w) => NatRepr n -> SwrappedInterval w -> SwrappedInterval n
trunc n sw
  | isBottom sw = bottom n
  | isTop sw = top n
  | otherwise =
      let w = swWidth sw
          widthInt = fromIntegral (natValue w) :: Int
          nInt = fromIntegral (natValue n) :: Int
          maskLower = bit nInt - 1
          -- Check hemisphere 0
          res0 = if bottom0 sw
                 then top n
                 else let start0 = swStart0 sw
                          end0 = swEnd0 sw
                          -- Check if upper bits are constant
                          upperStart = start0 `shiftR` nInt
                          upperEnd = end0 `shiftR` nInt
                       in if upperStart == upperEnd
                          -- Upper bits constant: keep lower bits
                          then let lowerStart = start0 .&. maskLower
                                   lowerEnd = end0 .&. maskLower
                                in if lowerStart <= lowerEnd
                                   then split n lowerStart lowerEnd
                                   else split n lowerStart lowerEnd  -- Wrapped
                          else if upperStart + 1 == upperEnd ||
                                  (upperStart == swMaxUnsigned w `shiftR` nInt && upperEnd == 0)
                               -- Upper bits differ by 1 (wrapping case)
                               then let lowerStart = start0 .&. maskLower
                                        lowerEnd = end0 .&. maskLower
                                     in if Prelude.not (lowerStart <= lowerEnd)
                                        then split n lowerStart lowerEnd
                                        else top n
                               else top n
          -- Check hemisphere 1
          res1 = if bottom1 sw
                 then top n
                 else let start1 = swStart1 sw
                          end1 = swEnd1 sw
                          upperStart = start1 `shiftR` nInt
                          upperEnd = end1 `shiftR` nInt
                       in if upperStart == upperEnd
                          then let lowerStart = start1 .&. maskLower
                                   lowerEnd = end1 .&. maskLower
                                in if lowerStart <= lowerEnd
                                   then split n lowerStart lowerEnd
                                   else split n lowerStart lowerEnd
                          else if upperStart + 1 == upperEnd ||
                                  (upperStart == swMaxUnsigned w `shiftR` nInt && upperEnd == 0)
                               then let lowerStart = start1 .&. maskLower
                                        lowerEnd = end1 .&. maskLower
                                     in if Prelude.not (lowerStart <= lowerEnd)
                                        then split n lowerStart lowerEnd
                                        else top n
                               else top n
       in join res0 res1

-- | Rotate left (conservative: returns top for non-trivial rotations)
rol :: (1 <= w) => SwrappedInterval w -> Integer -> SwrappedInterval w
rol sw k
  | isBottom sw = sw
  | k <= 0 = sw
  | otherwise = top (swWidth sw)  -- Conservative: rotations are imprecise

-- | Rotate right (conservative: returns top for non-trivial rotations)
ror :: (1 <= w) => SwrappedInterval w -> Integer -> SwrappedInterval w
ror sw k
  | isBottom sw = sw
  | k <= 0 = sw
  | otherwise = top (swWidth sw)  -- Conservative: rotations are imprecise

--------------------------------------------------------------------------------
-- Bounds extraction

-- | Get signed minimum value
getSignedMin :: (1 <= w) => SwrappedInterval w -> Maybe Integer
getSignedMin sw
  | isBottom sw = Nothing
  | Prelude.not (bottom1 sw) = Just (swToSigned (swWidth sw) (swStart1 sw))
  | Prelude.not (bottom0 sw) = Just (swToSigned (swWidth sw) (swStart0 sw))
  | otherwise = Nothing

-- | Get signed maximum value
getSignedMax :: (1 <= w) => SwrappedInterval w -> Maybe Integer
getSignedMax sw
  | isBottom sw = Nothing
  | Prelude.not (bottom0 sw) = Just (swToSigned (swWidth sw) (swEnd0 sw))
  | Prelude.not (bottom1 sw) = Just (swToSigned (swWidth sw) (swEnd1 sw))
  | otherwise = Nothing

-- | Get unsigned minimum value
getUnsignedMin :: (1 <= w) => SwrappedInterval w -> Maybe Integer
getUnsignedMin sw
  | isBottom sw = Nothing
  | Prelude.not (bottom0 sw) = Just (swStart0 sw)
  | Prelude.not (bottom1 sw) = Just (swStart1 sw)
  | otherwise = Nothing

-- | Get unsigned maximum value
getUnsignedMax :: (1 <= w) => SwrappedInterval w -> Maybe Integer
getUnsignedMax sw
  | isBottom sw = Nothing
  | Prelude.not (bottom1 sw) = Just (swEnd1 sw)
  | Prelude.not (bottom0 sw) = Just (swEnd0 sw)
  | otherwise = Nothing

--------------------------------------------------------------------------------
-- Transfer functions

-- | Transfer function for unsigned less-than
transferUlt :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> Maybe Bool
transferUlt sw1 sw2 =
  case (getUnsignedMax sw1, getUnsignedMin sw2) of
    (Just max1, Just min2) | max1 < min2 -> Just True
    _ -> case (getUnsignedMin sw1, getUnsignedMax sw2) of
          (Just min1, Just max2) | min1 >= max2 -> Just False
          _ -> Nothing

-- | Transfer function for signed less-than
transferSlt :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> Maybe Bool
transferSlt sw1 sw2 =
  case (getSignedMax sw1, getSignedMin sw2) of
    (Just max1, Just min2) | max1 < min2 -> Just True
    _ -> case (getSignedMin sw1, getSignedMax sw2) of
          (Just min1, Just max2) | min1 >= max2 -> Just False
          _ -> Nothing

-- | Lower half-line refinement (conservative implementation)
lowerHalfLine :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> Bool -> SwrappedInterval w
lowerHalfLine _y _x _isSigned =
  -- Conservative: return top
  -- Full implementation would refine y to [x_min, y_max]
  top (swWidth _y)

-- | Upper half-line refinement (conservative implementation)
upperHalfLine :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> Bool -> SwrappedInterval w
upperHalfLine _y _x _isSigned =
  -- Conservative: return top
  -- Full implementation would refine y to [y_min, x_max]
  top (swWidth _y)

--------------------------------------------------------------------------------
-- Test generators

-- | Generate random SwrappedInterval
genSwrappedInterval :: (1 <= w) => NatRepr w -> Gen (SwrappedInterval w)
genSwrappedInterval w = do
  r <- chooseInteger (0, 10)
  if r == 0
    then Prelude.pure $ bottom w
    else if r == 1
    then Prelude.pure $ top w
    else do
      let half = halfRange w
          maxVal = swMaxUnsigned w
          widthInt = fromIntegral (natValue w) :: Int
      -- Generate hemisphere 0 - use bit-based generation for efficiency
      h0Bottom <- (== 0) <$> chooseInteger (0, 1)
      h0Start <- if h0Bottom then Prelude.pure 0
                 else do
                   -- Generate start with widthInt-1 bits
                   bits <- chooseInteger (0, bit (widthInt - 1) - 1)
                   Prelude.pure (bits .&. (half - 1))
      h0End <- if h0Bottom then Prelude.pure 0
               else do
                 -- Generate offset from start (max 255 for efficiency)
                 offset <- chooseInteger (0, min 255 ((half - 1) - h0Start))
                 Prelude.pure (h0Start + offset)
      -- Generate hemisphere 1
      h1Bottom <- (== 0) <$> chooseInteger (0, 1)
      h1Start <- if h1Bottom then Prelude.pure half
                 else do
                   -- Generate start in upper half
                   bits <- chooseInteger (0, bit (widthInt - 1) - 1)
                   Prelude.pure (half + (bits .&. (half - 1)))
      h1End <- if h1Bottom then Prelude.pure half
               else do
                 -- Generate offset from start (max 255 for efficiency)
                 offset <- chooseInteger (0, min 255 (maxVal - h1Start))
                 Prelude.pure (h1Start + offset)
      -- Ensure not both bottom
      let (h0B, h1B) = if h0Bottom && h1Bottom then (False, h1Bottom) else (h0Bottom, h1Bottom)
      Prelude.pure $ SwrappedInterval h0Start h0End h0B h1Start h1End h1B w

-- | Generate SwrappedInterval and a member of that interval
genSwrappedIntervalPair :: (1 <= w) => NatRepr w -> Gen (SwrappedInterval w, Integer)
genSwrappedIntervalPair w = do
  r <- chooseInteger (0, 9)
  if r == 0
    then do
      -- Generate top and a random member
      let widthInt = fromIntegral (natValue w) :: Int
      bits <- chooseInteger (0, bit widthInt - 1)
      let x = bits .&. swMaxUnsigned w
      Prelude.pure (top w, x)
    else do
      -- Generate a random value first
      let widthInt = fromIntegral (natValue w) :: Int
          maxVal = swMaxUnsigned w
          half = halfRange w
      bits <- chooseInteger (0, bit widthInt - 1)
      let x = bits .&. maxVal
          msb = Bits.testBit x (widthInt - 1)

      -- Create an interval containing x
      if msb
        then do
          -- x is in hemisphere 1
          startOffset <- chooseInteger (0, min 255 (x - half))
          endOffset <- chooseInteger (0, min 255 (maxVal - x))
          let start1 = x - startOffset
              end1 = x + endOffset
          -- Maybe also include hemisphere 0
          includeH0 <- (== 0) <$> chooseInteger (0, 2)
          if includeH0
            then do
              start0 <- chooseInteger (0, min 255 (half - 1))
              endOff <- chooseInteger (0, min 255 ((half - 1) - start0))
              let end0 = start0 + endOff
              Prelude.pure (SwrappedInterval start0 end0 False start1 end1 False w, x)
            else
              Prelude.pure (SwrappedInterval 0 0 True start1 end1 False w, x)
        else do
          -- x is in hemisphere 0
          startOffset <- chooseInteger (0, min 255 x)
          endOffset <- chooseInteger (0, min 255 ((half - 1) - x))
          let start0 = x - startOffset
              end0 = x + endOffset
          -- Maybe also include hemisphere 1
          includeH1 <- (== 0) <$> chooseInteger (0, 2)
          if includeH1
            then do
              start1 <- chooseInteger (half, half + min 255 (maxVal - half))
              endOff <- chooseInteger (0, min 255 (maxVal - start1))
              let end1 = start1 + endOff
              Prelude.pure (SwrappedInterval start0 end0 False start1 end1 False w, x)
            else
              Prelude.pure (SwrappedInterval start0 end0 False half half True w, x)

--------------------------------------------------------------------------------
-- Correctness properties

-- | Soundness property: singleton contains the given value
correct_singleton :: (1 <= w) => NatRepr w -> Integer -> Property
correct_singleton w x =
  property $ member (singleton w x) x

-- | Soundness property: membership test is sound
correct_member :: (1 <= w) => (SwrappedInterval w, Integer) -> Property
correct_member (sw, x) =
  property $ member sw x

-- | Soundness property: split function creates valid intervals
correct_split :: (1 <= w) => NatRepr w -> Integer -> Integer -> Integer -> Property
correct_split w start end x =
  let maxVal = swMaxUnsigned w
      start' = start .&. maxVal
      end' = end .&. maxVal
      x' = x .&. maxVal
      sw = split w start' end'
      -- If x is in [start, end] modulo wrapping, it should be in sw
      inRange = if start' <= end'
                then start' <= x' && x' <= end'
                else x' >= start' || x' <= end'
   in property $ if inRange then member sw x' else True

-- | Soundness property: fromRange contains all values in range
correct_from_range :: (1 <= w) => NatRepr w -> Integer -> Integer -> Integer -> Property
correct_from_range w lo hi x =
  let maxVal = swMaxUnsigned w
      lo' = lo .&. maxVal
      hi' = hi .&. maxVal
      x' = x .&. maxVal
      sw = fromRange w lo' hi'
   in property $ if lo' <= x' && x' <= hi'
                 then member sw x'
                 else True

-- | Soundness property: join contains both inputs
correct_join :: (1 <= w) => (SwrappedInterval w, Integer) -> (SwrappedInterval w, Integer) -> Property
correct_join (sw1, x) (sw2, _y) =
  property $ member (join sw1 sw2) x

-- | Soundness property: meet is intersection
correct_meet :: (1 <= w) => (SwrappedInterval w, Integer) -> (SwrappedInterval w, Integer) -> Property
correct_meet (sw1, x) (sw2, y) =
  let m = meet sw1 sw2
   in property $ if x == y then member m x else True

-- | Soundness property: subsumption
correct_le :: (1 <= w) => (SwrappedInterval w, Integer) -> (SwrappedInterval w, Integer) -> Property
correct_le (sw1, x) (sw2, _y) =
  property $ if sw1 `le` sw2 then member sw2 x else True

-- | Soundness property: addition
correct_add :: (1 <= w) => (SwrappedInterval w, Integer) -> (SwrappedInterval w, Integer) -> Property
correct_add (sw1, x) (sw2, y) =
  let w = swWidth sw1
      maxVal = swMaxUnsigned w
      result = (x + y) .&. maxVal
   in property $ member (add sw1 sw2) result

-- | Soundness property: negation
correct_neg :: (1 <= w) => (SwrappedInterval w, Integer) -> Property
correct_neg (sw, x) =
  let w = swWidth sw
      maxVal = swMaxUnsigned w
      result = (Prelude.negate x) .&. maxVal
   in property $ member (neg sw) result

-- | Soundness property: subtraction
correct_sub :: (1 <= w) => (SwrappedInterval w, Integer) -> (SwrappedInterval w, Integer) -> Property
correct_sub (sw1, x) (sw2, y) =
  let w = swWidth sw1
      maxVal = swMaxUnsigned w
      result = (x - y) .&. maxVal
   in property $ member (sub sw1 sw2) result

-- | Soundness property: multiplication
correct_mul :: (1 <= w) => (SwrappedInterval w, Integer) -> (SwrappedInterval w, Integer) -> Property
correct_mul (sw1, x) (sw2, y) =
  let w = swWidth sw1
      maxVal = swMaxUnsigned w
      result = (x * y) .&. maxVal
   in property $ member (mul sw1 sw2) result

-- | Soundness property: unsigned division
correct_udiv :: (1 <= w) => (SwrappedInterval w, Integer) -> (SwrappedInterval w, Integer) -> Property
correct_udiv (sw1, x) (sw2, y) =
  let w = swWidth sw1
      maxVal = swMaxUnsigned w
   in if y == 0
      then property True
      else let result = (x `div` y) .&. maxVal
            in property $ member (udiv sw1 sw2) result

-- | Soundness property: signed division
correct_sdiv :: (1 <= w) => (SwrappedInterval w, Integer) -> (SwrappedInterval w, Integer) -> Property
correct_sdiv (sw1, x) (sw2, y) =
  let w = swWidth sw1
      maxVal = swMaxUnsigned w
      xs = swToSigned w x
      ys = swToSigned w y
   in if ys == 0
      then property True
      else let result = (xs `quot` ys) .&. maxVal
            in property $ member (sdiv sw1 sw2) result

-- | Soundness property: unsigned remainder
correct_urem :: (1 <= w) => (SwrappedInterval w, Integer) -> (SwrappedInterval w, Integer) -> Property
correct_urem (sw1, x) (sw2, y) =
  let w = swWidth sw1
      maxVal = swMaxUnsigned w
   in if y == 0
      then property True
      else let result = (x `mod` y) .&. maxVal
            in property $ member (urem sw1 sw2) result

-- | Soundness property: signed remainder
correct_srem :: (1 <= w) => (SwrappedInterval w, Integer) -> (SwrappedInterval w, Integer) -> Property
correct_srem (sw1, x) (sw2, y) =
  let w = swWidth sw1
      maxVal = swMaxUnsigned w
      xs = swToSigned w x
      ys = swToSigned w y
   in if ys == 0
      then property True
      else let result = (xs `rem` ys) .&. maxVal
            in property $ member (srem sw1 sw2) result

-- | Soundness property: bitwise AND
correct_and :: (1 <= w) => (SwrappedInterval w, Integer) -> (SwrappedInterval w, Integer) -> Property
correct_and (sw1, x) (sw2, y) =
  property $ member (and sw1 sw2) (x .&. y)

-- | Soundness property: bitwise OR
correct_or :: (1 <= w) => (SwrappedInterval w, Integer) -> (SwrappedInterval w, Integer) -> Property
correct_or (sw1, x) (sw2, y) =
  property $ member (or sw1 sw2) (x .|. y)

-- | Soundness property: bitwise XOR
correct_xor :: (1 <= w) => (SwrappedInterval w, Integer) -> (SwrappedInterval w, Integer) -> Property
correct_xor (sw1, x) (sw2, y) =
  property $ member (xor sw1 sw2) (Bits.xor x y)

-- | Soundness property: bitwise NOT
correct_not :: (1 <= w) => (SwrappedInterval w, Integer) -> Property
correct_not (sw, x) =
  let w = swWidth sw
      maxVal = swMaxUnsigned w
      result = (complement x) .&. maxVal
   in property $ member (not sw) result

-- | Soundness property: left shift
correct_shl :: (1 <= w) => (SwrappedInterval w, Integer) -> Integer -> Property
correct_shl (sw, x) k =
  let w = swWidth sw
      maxVal = swMaxUnsigned w
      k' = fromIntegral (min (max 0 k) (fromIntegral (natValue w) - 1)) :: Int
      result = (x `shiftL` k') .&. maxVal
   in property $ member (shl sw k) result

-- | Soundness property: logical right shift
correct_lshr :: (1 <= w) => (SwrappedInterval w, Integer) -> Integer -> Property
correct_lshr (sw, x) k =
  let k' = fromIntegral (min (max 0 k) (fromIntegral (natValue (swWidth sw)) - 1)) :: Int
      result = x `shiftR` k'
   in property $ member (lshr sw k) result

-- | Soundness property: arithmetic right shift
correct_ashr :: (1 <= w) => (SwrappedInterval w, Integer) -> Integer -> Property
correct_ashr (sw, x) k =
  let w = swWidth sw
      widthInt = fromIntegral (natValue w) :: Int
      maxVal = swMaxUnsigned w
      k' = fromIntegral (min (max 0 k) (fromIntegral (natValue w) - 1)) :: Int
      xs = swToSigned w x
      result = (xs `shiftR` k') .&. maxVal
   in property $ member (ashr sw k) result

-- | Soundness property: zero extension
correct_zext :: (1 <= w, 1 <= u, w+1 <= u) => NatRepr u -> (SwrappedInterval w, Integer) -> Property
correct_zext u (sw, x) =
  property $ member (zext sw u) x

-- | Soundness property: sign extension
correct_sext :: (1 <= w, 1 <= u, w+1 <= u) => NatRepr u -> (SwrappedInterval w, Integer) -> Property
correct_sext u (sw, x) =
  let w = swWidth sw
      widthInt = fromIntegral (natValue w) :: Int
      widthU = fromIntegral (natValue u) :: Int
      signBits = Bits.xor ((bit widthU :: Integer) - 1) ((bit widthInt :: Integer) - 1)
      xSigned = if Bits.testBit x (widthInt - 1)
                then x .|. signBits
                else x
      maxVal = swMaxUnsigned u
   in property $ member (sext sw u) (xSigned .&. maxVal)

-- | Soundness property: truncation
correct_trunc :: (1 <= n, n+1 <= w) => NatRepr n -> (SwrappedInterval w, Integer) -> Property
correct_trunc n (sw, x) =
  let maxVal = swMaxUnsigned n
   in property $ member (trunc n sw) (x .&. maxVal)

-- | Soundness property: rotate left
correct_rol :: (1 <= w) => (SwrappedInterval w, Integer) -> Integer -> Property
correct_rol (sw, x) k =
  let w = swWidth sw
      widthInt = fromIntegral (natValue w) :: Int
      maxVal = swMaxUnsigned w
      k' = fromIntegral (k `mod` fromIntegral widthInt) :: Int
      result = ((x `shiftL` k') .|. (x `shiftR` (widthInt - k'))) .&. maxVal
   in property $ member (rol sw k) result

-- | Soundness property: rotate right
correct_ror :: (1 <= w) => (SwrappedInterval w, Integer) -> Integer -> Property
correct_ror (sw, x) k =
  let w = swWidth sw
      widthInt = fromIntegral (natValue w) :: Int
      maxVal = swMaxUnsigned w
      k' = fromIntegral (k `mod` fromIntegral widthInt) :: Int
      result = ((x `shiftR` k') .|. (x `shiftL` (widthInt - k'))) .&. maxVal
   in property $ member (ror sw k) result

--------------------------------------------------------------------------------
-- Lattice property tests

-- | Join commutativity
lattice_join_commutative :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> Property
lattice_join_commutative sw1 sw2 =
  property $ join sw1 sw2 == join sw2 sw1

-- | Meet commutativity
lattice_meet_commutative :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> Property
lattice_meet_commutative sw1 sw2 =
  property $ meet sw1 sw2 == meet sw2 sw1

-- | Join associativity
lattice_join_associative :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> SwrappedInterval w -> Property
lattice_join_associative sw1 sw2 sw3 =
  property $ join sw1 (join sw2 sw3) == join (join sw1 sw2) sw3

-- | Meet associativity
lattice_meet_associative :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> SwrappedInterval w -> Property
lattice_meet_associative sw1 sw2 sw3 =
  property $ meet sw1 (meet sw2 sw3) == meet (meet sw1 sw2) sw3

-- | Join idempotence
lattice_join_idempotent :: (1 <= w) => SwrappedInterval w -> Property
lattice_join_idempotent sw =
  property $ join sw sw == sw

-- | Meet idempotence
lattice_meet_idempotent :: (1 <= w) => SwrappedInterval w -> Property
lattice_meet_idempotent sw =
  property $ meet sw sw == sw

-- | Absorption law 1
lattice_absorption1 :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> Property
lattice_absorption1 sw1 sw2 =
  property $ join sw1 (meet sw1 sw2) == sw1

-- | Absorption law 2
lattice_absorption2 :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> Property
lattice_absorption2 sw1 sw2 =
  property $ meet sw1 (join sw1 sw2) == sw1

-- | LE reflexivity
lattice_le_reflexive :: (1 <= w) => SwrappedInterval w -> Property
lattice_le_reflexive sw =
  property $ sw `le` sw

-- | LE antisymmetry
lattice_le_antisymmetric :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> Property
lattice_le_antisymmetric sw1 sw2 =
  property $ if sw1 `le` sw2 && sw2 `le` sw1 then sw1 == sw2 else True

-- | LE transitivity
lattice_le_transitive :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> SwrappedInterval w -> Property
lattice_le_transitive sw1 sw2 sw3 =
  property $ if sw1 `le` sw2 && sw2 `le` sw3 then sw1 `le` sw3 else True

-- | Join upper bound 1
lattice_join_upper_bound1 :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> Property
lattice_join_upper_bound1 sw1 sw2 =
  property $ sw1 `le` join sw1 sw2

-- | Join upper bound 2
lattice_join_upper_bound2 :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> Property
lattice_join_upper_bound2 sw1 sw2 =
  property $ sw2 `le` join sw1 sw2

-- | Meet lower bound 1
lattice_meet_lower_bound1 :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> Property
lattice_meet_lower_bound1 sw1 sw2 =
  property $ meet sw1 sw2 `le` sw1

-- | Meet lower bound 2
lattice_meet_lower_bound2 :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> Property
lattice_meet_lower_bound2 sw1 sw2 =
  property $ meet sw1 sw2 `le` sw2

-- | Join least upper bound
lattice_join_least_upper_bound :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> SwrappedInterval w -> Property
lattice_join_least_upper_bound sw1 sw2 sw3 =
  property $ if sw1 `le` sw3 && sw2 `le` sw3 then join sw1 sw2 `le` sw3 else True

-- | Meet greatest lower bound
lattice_meet_greatest_lower_bound :: (1 <= w) => SwrappedInterval w -> SwrappedInterval w -> SwrappedInterval w -> Property
lattice_meet_greatest_lower_bound sw1 sw2 sw3 =
  property $ if sw3 `le` sw1 && sw3 `le` sw2 then sw3 `le` meet sw1 sw2 else True

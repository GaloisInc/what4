{-|
Module      : What4.Utils.BVDomain.SWB
Copyright   : (c) Galois Inc, 2025
License     : BSD3
Maintainer  : langston@galois.com

Provides SWB (Signedness-Aware Word and Bit-Level) abstract domain for bitvectors.

SWB is a reduced product that combines two complementary abstractions:
- Stnum: Provides bit-level precision (which bits are definitely 0, 1, or unknown)
- SwrappedInterval: Provides word-level precision (range bounds for numeric values)

The reduced product uses a bidirectional synchronization algorithm to ensure both
domains agree, providing tighter bounds than either domain alone.

Based on algorithms from:
- Clam static analyzer (crab/domains/switv_stnum_domain.hpp)
- "Signedness-Agnostic Program Analysis" (ISSTA 2025)

= Implementation Notes

This implementation closely follows the Clam reference with precision improvements:

* __Improved bitwise operations__: The @and@ and @or@ operations now use the
  precise Stnum implementations (matching Clam stnum_impl.hpp:1274-1293)
  instead of conservatively using @Stnum.top@. While the SwrappedInterval
  component remains conservative (matching the Clam reference), the Stnum
  component now provides bit-level precision by tracking which hemisphere
  results belong to.

* __Three-phase reduction__: The @reduce@ function implements bidirectional
  synchronization between Stnum and SwrappedInterval:

  1. Extract bounds from both domains
  2. Convert bounds to the opposite domain representation
  3. Refine each domain by meeting with the converted bounds

  This ensures both domains agree and provides tighter analysis results.

* __Conservative by design__: Some operations (like SwrappedInterval bitwise
  ops) are intentionally conservative, matching the Clam reference. The reduced
  product still provides value through the Stnum component's precision.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module What4.Utils.BVDomain.SWB
  ( -- * SWB type
    SWB(..)
  , bottom, top, singleton, fromRange
  , isBottom, isTop, member, proper, asSingleton
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
    -- * Testing support
  , genSWB, genSWBPair
    -- * Correctness properties
  , correct_singleton
  , correct_member
  , correct_from_range
  , correct_reduce_idempotent
  , correct_join
  , correct_meet
  , correct_le
  , correct_add
  , correct_neg
  , correct_sub
  , correct_mul
  , correct_and
  , correct_or
  , correct_xor
  , correct_not
  , correct_shl
  , correct_lshr
  , correct_ashr
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

import qualified What4.Utils.BVDomain.Stnum as Stnum
import           What4.Utils.BVDomain.Stnum (Stnum(..))
import qualified What4.Utils.BVDomain.SwrappedInterval as SW
import           What4.Utils.BVDomain.SwrappedInterval (SwrappedInterval(..))
import qualified What4.Utils.BVDomain.Tnum as Tnum
import           What4.Utils.BVDomain.Tnum (Tnum, pattern TnumBottom, pattern TnumValue)

--------------------------------------------------------------------------------
-- SWB definition

-- | SWB Domain: Reduced product of Stnum (bit-level) and SwrappedInterval (word-level)
--
-- Invariant: The two domains must be consistent (reduced).
-- This invariant is maintained by the 'reduce' function.
data SWB (w :: Nat) = SWB
  { swbStnum    :: !(Stnum w)             -- ^ Bit-level domain
  , swbInterval :: !(SwrappedInterval w)  -- ^ Word-level domain
  }

deriving instance Show (SWB w)

-- | Equality for SWB values
instance Eq (SWB w) where
  SWB st1 sw1 == SWB st2 sw2 = st1 == st2 && sw1 == sw2

--------------------------------------------------------------------------------
-- Helper functions

-- | Get the bitvector width
swbWidth :: SWB w -> NatRepr w
swbWidth (SWB st _) = Stnum.width st

-- | Maximum unsigned value for width w: 2^w - 1
bvdMask :: NatRepr w -> Integer
bvdMask w = bit (fromIntegral (natValue w)) - 1

-- | Half range for width w: 2^(w-1)
halfRange :: NatRepr w -> Integer
halfRange w = bit (fromIntegral (natValue w) - 1)

-- | Convert an interval [min, max] to a tnum representation.
--
-- The tnum captures all values in the range with a value/mask pair:
-- - Common prefix bits → set in value, clear in mask (known)
-- - Differing bits → set in mask (unknown)
--
-- Example: [0x50, 0x5F] (01010000 to 01011111)
--   XOR: 0x0F (00001111) - bits 0-3 differ
--   Mask: (1 << 4) - 1 = 0x0F
--   Common prefix: 0x50 & ~0x0F = 0x50
--   Result: value=0x50, mask=0x0F
--
-- Based on Clam stnum_impl.hpp:162-182 (tnum_from_range_s)
tnumFromRange :: (1 <= w) => NatRepr w -> Integer -> Integer -> Tnum w
tnumFromRange w lo hi
  | lo > hi   = Tnum.bottom w  -- Invalid range
  | lo == hi  = Tnum.singleton w lo  -- Single value
  | otherwise =
      let -- Mask to width
          widthInt = fromIntegral (natValue w) :: Int
          widthMask = bvdMask w
          lo' = lo .&. widthMask
          hi' = hi .&. widthMask

          -- XOR to find differing bits (chi in reference)
          chi = lo' `Bits.xor` hi'

          -- Find the bit size (fls() in reference): number of bits needed
          -- fls returns 1-indexed position of highest bit
          -- Example: fls(4) = 3 because 0b100 needs 3 bits
          bits = fls chi

          -- Check if bits exceeds width-1 (i.e., bits >= width)
          -- This happens when the range crosses hemisphere boundaries
          half = bit (widthInt - 1)
          maxInHalf = half - 1

       in if bits > widthInt - 1  -- equivalent to bits >= widthInt
          then -- Range is too large, return appropriate hemisphere top
               if Bits.testBit lo' (widthInt - 1)  -- min.msb()
               then TnumValue w half maxInHalf  -- Negative hemisphere top
               else TnumValue w 0 maxInHalf     -- Non-negative hemisphere top
          else -- Create delta = (1 << bits) - 1
               let delta = (bit bits) - 1
                   -- Value: lo with unknown bits zeroed (lo & ~delta)
                   value = lo' .&. complement delta
                in TnumValue w value delta

-- | Helper: find the number of bits needed to represent value (fls in reference)
-- Returns the 1-indexed position of the highest set bit
-- Example: fls 0x0100 = 9 (binary 100000000 needs 9 bits)
-- Example: fls 0x000F = 4 (binary 1111 needs 4 bits)
-- Example: fls 0x0004 = 3 (binary 100 needs 3 bits)
-- Example: fls 0x0001 = 1 (binary 1 needs 1 bit)
-- Example: fls 0x0000 = 0
fls :: Integer -> Int
fls 0 = 0
fls n = go 0 n
  where
    go acc 0 = acc
    go acc x = go (acc + 1) (x `shiftR` 1)

--------------------------------------------------------------------------------
-- The critical reduce algorithm

-- | Refine intervals with bounds extracted from bit-level domain
swRefineWithBounds :: (1 <= w)
                   => SwrappedInterval w
                   -> Integer  -- h0_min
                   -> Integer  -- h0_max
                   -> Integer  -- h1_min
                   -> Integer  -- h1_max
                   -> SwrappedInterval w
swRefineWithBounds sw h0_min h0_max h1_min h1_max =
  -- Only refine if hemisphere is not bottom
  let sw0' = if SW.bottom0 sw then sw
             else sw { SW.swStart0 = max (SW.swStart0 sw) h0_min
                     , SW.swEnd0   = min (SW.swEnd0 sw) h0_max
                     }
      sw1' = if SW.bottom1 sw0' then sw0'
             else sw0' { SW.swStart1 = max (SW.swStart1 sw0') h1_min
                       , SW.swEnd1   = min (SW.swEnd1 sw0') h1_max
                       }
  in sw1'

-- | Reduce SWB: synchronize bit-level and word-level domains
--
-- Performs bidirectional synchronization with internal refinement loop:
-- For each hemisphere:
--   1. Extract bounds from stnum → refine swrapped_interval
--   2. Convert swrapped_interval back to tnum → meet with stnum
--   3. Extract bounds from refined stnum → refine swrapped_interval again
--
-- Based on Clam switv_stnum_domain.hpp:78-290 (reduce_variable method)
reduce :: (1 <= w) => SWB w -> SWB w
reduce swb@(SWB st sw)
  -- Handle bottom propagation
  | Stnum.isBottom st || SW.isBottom sw =
      let w = swbWidth swb
       in SWB (Stnum.bottom w) (SW.bottom w)
  | otherwise =
      let w = swbWidth swb

          -- Get initial hemispheres
          h0 = Stnum.stnumHemi0 st
          h1 = Stnum.stnumHemi1 st

          -- Process hemisphere 0
          (sw_start0, sw_end0, st0_refined) =
            if SW.bottom0 sw || Tnum.isBottom h0
            then -- Make both domains bottom for this hemisphere
                 let half = halfRange w
                  in (half - 1, 0, Tnum.bottom w)  -- start > end makes interval bottom
            else
              let -- Step 1: Extract bounds from stnum and refine interval
                  TnumValue _ v0 m0 = h0
                  st0_min = v0
                  st0_max = v0 + m0
                  sw0_start = max (SW.swStart0 sw) st0_min
                  sw0_end = min (SW.swEnd0 sw) st0_max

                  -- Step 2: Convert interval back to tnum and meet
                  range0_tnum = tnumFromRange w sw0_start sw0_end
                  st0_met = Tnum.meet h0 range0_tnum

                  -- Step 3: Extract bounds from refined stnum and refine interval again
                  (sw0_start', sw0_end') =
                    if Tnum.isBottom st0_met
                    then (sw0_start, sw0_end)
                    else case st0_met of
                           TnumValue _ v0' m0' ->
                             let st0_min' = v0'
                                 st0_max' = v0' + m0'
                              in (max sw0_start st0_min', min sw0_end st0_max')
                           _ -> (sw0_start, sw0_end)
               in (sw0_start', sw0_end', st0_met)

          -- Process hemisphere 1
          (sw_start1, sw_end1, st1_refined) =
            if SW.bottom1 sw || Tnum.isBottom h1
            then -- Make both domains bottom for this hemisphere
                 (bvdMask w, halfRange w, Tnum.bottom w)  -- start > end makes interval bottom
            else
              let -- Step 1: Extract bounds from stnum and refine interval
                  TnumValue _ v1 m1 = h1
                  st1_min = v1
                  st1_max = v1 + m1
                  sw1_start = max (SW.swStart1 sw) st1_min
                  sw1_end = min (SW.swEnd1 sw) st1_max

                  -- Step 2: Convert interval back to tnum and meet
                  range1_tnum = tnumFromRange w sw1_start sw1_end
                  st1_met = Tnum.meet h1 range1_tnum

                  -- Step 3: Extract bounds from refined stnum and refine interval again
                  (sw1_start', sw1_end') =
                    if Tnum.isBottom st1_met
                    then (sw1_start, sw1_end)
                    else case st1_met of
                           TnumValue _ v1' m1' ->
                             let st1_min' = v1'
                                 st1_max' = v1' + m1'
                              in (max sw1_start st1_min', min sw1_end st1_max')
                           _ -> (sw1_start, sw1_end)
               in (sw1_start', sw1_end', st1_met)

          -- Build refined domains
          -- Check if intervals are valid (start <= end) or should be marked bottom
          h0_bottom = Tnum.isBottom st0_refined || sw_start0 > sw_end0
          h1_bottom = Tnum.isBottom st1_refined || sw_start1 > sw_end1

          sw_refined = sw { SW.swStart0 = sw_start0
                         , SW.swEnd0 = sw_end0
                         , SW.bottom0 = h0_bottom
                         , SW.swStart1 = sw_start1
                         , SW.swEnd1 = sw_end1
                         , SW.bottom1 = h1_bottom
                         }
          st_refined = Stnum st0_refined st1_refined
       in SWB st_refined sw_refined

--------------------------------------------------------------------------------
-- Basic constructors and queries

-- | Bottom element (empty set)
bottom :: (1 <= w) => NatRepr w -> SWB w
bottom w = SWB (Stnum.bottom w) (SW.bottom w)

-- | Top element (all values)
top :: (1 <= w) => NatRepr w -> SWB w
top w = SWB (Stnum.top w) (SW.top w)

-- | Singleton SWB representing exactly one value
singleton :: (1 <= w) => NatRepr w -> Integer -> SWB w
singleton w x = reduce $ SWB (Stnum.singleton w x) (SW.singleton w x)

-- | Create SWB from a range [lo, hi]
--
-- Based on Clam stnum_impl.hpp:124-159 (mk_stnum with bounds)
fromRange :: (1 <= w) => NatRepr w -> Integer -> Integer -> SWB w
fromRange w lo hi =
  let widthInt = fromIntegral (natValue w) :: Int
      maxVal = bvdMask w
      lo' = lo .&. maxVal
      hi' = hi .&. maxVal
      loMsb = Bits.testBit lo' (widthInt - 1)
      hiMsb = Bits.testBit hi' (widthInt - 1)
      half = halfRange w

      -- Construct stnum based on which hemispheres the bounds are in
      -- This must match the cases in SW.split (lines 271-285)
      st = if Prelude.not loMsb && Prelude.not hiMsb
           then -- Both in hemisphere 0
                if lo' <= hi'
                then Stnum (tnumFromRange w lo' hi') (Tnum.bottom w)  -- Non-wrapped [lo, hi]
                else Stnum.top w  -- Wrapped around, return top
           else if Prelude.not loMsb && hiMsb
           then -- Crosses from hemi0 to hemi1 (non-wrapped range spanning sign bit)
                let tPos = tnumFromRange w lo' (half - 1)  -- Non-negative part: [lo, half-1]
                    tNeg = tnumFromRange w half hi'         -- Negative part: [half, hi]
                 in Stnum tPos tNeg
           else if loMsb && Prelude.not hiMsb
           then -- Wraps around 2^w
                let tPos = tnumFromRange w 0 hi'      -- Non-negative part: [0, hi]
                    tNeg = tnumFromRange w lo' maxVal -- Negative part: [lo, max]
                 in Stnum tPos tNeg
           else -- Both in hemisphere 1
                if lo' <= hi'
                then Stnum (Tnum.bottom w) (tnumFromRange w lo' hi')  -- Non-wrapped [lo, hi]
                else Stnum.top w  -- Wrapped around, return top

      sw = SW.fromRange w lo' hi'
   in reduce (SWB st sw)

-- | Check if SWB is bottom (empty set)
isBottom :: SWB w -> Bool
isBottom (SWB st _) = Stnum.isBottom st

-- | Check if SWB is top (all values)
isTop :: (1 <= w) => SWB w -> Bool
isTop (SWB st sw) = Stnum.le (Stnum.top (Stnum.width st)) st && SW.isTop sw

-- | Check if a value is a member of the SWB
member :: SWB w -> Integer -> Bool
member (SWB st sw) x = Stnum.member st x && SW.member sw x

-- | Check if SWB satisfies representation invariants
proper :: SWB w -> Bool
proper (SWB st sw) = Stnum.proper st && SW.proper sw

-- | Return value if this is a singleton
asSingleton :: SWB w -> Maybe Integer
asSingleton swb@(SWB st sw)
  | isBottom swb = Nothing
  | otherwise =
      -- Check both domains agree on singleton
      case (Stnum.member st <$> SW.asSingleton sw, SW.asSingleton sw) of
        (Just True, Just x) -> Just x
        _ -> Nothing

--------------------------------------------------------------------------------
-- Lattice operations

-- | Lattice join for SWB
--
-- Pattern: Apply operation to both domains, then reduce to maintain consistency.
join :: (1 <= w) => SWB w -> SWB w -> SWB w
join (SWB st1 sw1) (SWB st2 sw2) =
  reduce $ SWB (Stnum.join st1 st2) (SW.join sw1 sw2)

-- | Lattice meet for SWB
meet :: (1 <= w) => SWB w -> SWB w -> SWB w
meet (SWB st1 sw1) (SWB st2 sw2) =
  reduce $ SWB (Stnum.meet st1 st2) (SW.meet sw1 sw2)

-- | Subsumption test for SWB
--
-- x <= y iff both domains satisfy subsumption
le :: SWB w -> SWB w -> Bool
le (SWB st1 sw1) (SWB st2 sw2) =
  Stnum.le st1 st2 && SW.le sw1 sw2

--------------------------------------------------------------------------------
-- Arithmetic operations

-- | SWB addition
add :: (1 <= w) => SWB w -> SWB w -> SWB w
add (SWB st1 sw1) (SWB st2 sw2) =
  reduce $ SWB (Stnum.add st1 st2) (SW.add sw1 sw2)

-- | SWB negation
neg :: (1 <= w) => SWB w -> SWB w
neg (SWB st sw) =
  reduce $ SWB (Stnum.neg st) (SW.neg sw)

-- | SWB subtraction
sub :: (1 <= w) => SWB w -> SWB w -> SWB w
sub (SWB st1 sw1) (SWB st2 sw2) =
  reduce $ SWB (Stnum.sub st1 st2) (SW.sub sw1 sw2)

-- | SWB multiplication
mul :: (1 <= w) => SWB w -> SWB w -> SWB w
mul (SWB st1 sw1) (SWB st2 sw2) =
  reduce $ SWB (Stnum.mul st1 st2) (SW.mul sw1 sw2)

-- | SWB unsigned division
udiv :: (1 <= w) => SWB w -> SWB w -> SWB w
udiv (SWB st1 sw1) (SWB st2 sw2) =
  reduce $ SWB (Stnum.udiv st1 st2) (SW.udiv sw1 sw2)

-- | SWB signed division
sdiv :: (1 <= w) => SWB w -> SWB w -> SWB w
sdiv (SWB st1 sw1) (SWB st2 sw2) =
  reduce $ SWB (Stnum.sdiv st1 st2) (SW.sdiv sw1 sw2)

-- | SWB unsigned remainder
urem :: (1 <= w) => SWB w -> SWB w -> SWB w
urem (SWB st1 sw1) (SWB st2 sw2) =
  reduce $ SWB (Stnum.urem st1 st2) (SW.urem sw1 sw2)

-- | SWB signed remainder
srem :: (1 <= w) => SWB w -> SWB w -> SWB w
srem (SWB st1 sw1) (SWB st2 sw2) =
  reduce $ SWB (Stnum.srem st1 st2) (SW.srem sw1 sw2)

--------------------------------------------------------------------------------
-- Bitwise operations

-- | SWB bitwise AND
--
-- Uses Stnum.and from Clam stnum_impl.hpp:1274-1281.
-- SW.and is conservative (returns top), but Stnum.and provides better precision
-- by tracking which hemisphere the result belongs to.
and :: (1 <= w) => SWB w -> SWB w -> SWB w
and (SWB st1 sw1) (SWB st2 sw2) =
  reduce $ SWB (Stnum.and st1 st2) (SW.and sw1 sw2)

-- | SWB bitwise OR
--
-- Uses Stnum.or from Clam stnum_impl.hpp:1286-1293.
-- SW.or is conservative (returns top), but Stnum.or provides better precision
-- by tracking which hemisphere the result belongs to.
or :: (1 <= w) => SWB w -> SWB w -> SWB w
or (SWB st1 sw1) (SWB st2 sw2) =
  reduce $ SWB (Stnum.or st1 st2) (SW.or sw1 sw2)

-- | SWB bitwise XOR
xor :: (1 <= w) => SWB w -> SWB w -> SWB w
xor (SWB st1 sw1) (SWB st2 sw2) =
  reduce $ SWB (Stnum.xor st1 st2) (SW.xor sw1 sw2)

-- | SWB bitwise NOT
not :: (1 <= w) => SWB w -> SWB w
not (SWB st sw) =
  reduce $ SWB (Stnum.not st) (SW.not sw)

--------------------------------------------------------------------------------
-- Shift operations

-- | SWB left shift
shl :: (1 <= w) => SWB w -> Integer -> SWB w
shl (SWB st sw) k =
  reduce $ SWB (Stnum.shl st k) (SW.shl sw k)

-- | SWB logical right shift
lshr :: (1 <= w) => SWB w -> Integer -> SWB w
lshr (SWB st sw) k =
  reduce $ SWB (Stnum.lshr st k) (SW.lshr sw k)

-- | SWB arithmetic right shift
ashr :: (1 <= w) => SWB w -> Integer -> SWB w
ashr (SWB st sw) k =
  reduce $ SWB (Stnum.ashr st k) (SW.ashr sw k)

--------------------------------------------------------------------------------
-- Width operations

-- | SWB zero extension
zext :: (1 <= w, w+1 <= w', 1 <= w') => SWB w -> NatRepr w' -> SWB w'
zext (SWB st sw) w' =
  reduce $ SWB (Stnum.zext st w') (SW.zext sw w')

-- | SWB sign extension
sext :: (1 <= w, w+1 <= w', 1 <= w') => SWB w -> NatRepr w' -> SWB w'
sext (SWB st sw) w' =
  reduce $ SWB (Stnum.sext st w') (SW.sext sw w')

-- | SWB truncation
trunc :: (1 <= w, 1 <= w', w' + 1 <= w) => NatRepr w' -> SWB w -> SWB w'
trunc w' (SWB st sw) =
  reduce $ SWB (Stnum.trunc w' st) (SW.trunc w' sw)

-- | SWB rotate left
rol :: (1 <= w) => SWB w -> Integer -> SWB w
rol (SWB st sw) k =
  reduce $ SWB (Stnum.rol st k) (SW.rol sw k)

-- | SWB rotate right
ror :: (1 <= w) => SWB w -> Integer -> SWB w
ror (SWB st sw) k =
  reduce $ SWB (Stnum.ror st k) (SW.ror sw k)

--------------------------------------------------------------------------------
-- Testing support

-- | Generate arbitrary SWB values
genSWB :: (1 <= w) => NatRepr w -> Gen (SWB w)
genSWB w = do
  st <- Stnum.genStnum w
  sw <- SW.genSwrappedInterval w
  return $ reduce (SWB st sw)  -- Always reduce to maintain invariant

-- | Generate SWB value and a member
genSWBPair :: (1 <= w) => NatRepr w -> Gen (SWB w, Integer)
genSWBPair w = do
  val <- chooseInteger (0, bvdMask w)
  let swb = singleton w val
  return (swb, val)

--------------------------------------------------------------------------------
-- Correctness properties

-- Concrete semantics helpers
bvAdd, bvSub, bvMul, bvUDiv, bvSDiv, bvURem, bvSRem :: NatRepr w -> Integer -> Integer -> Integer
bvAdd w x y = (x + y) .&. bvdMask w
bvSub w x y = (x - y) .&. bvdMask w
bvMul w x y = (x * y) .&. bvdMask w
bvUDiv w x y = if y == 0 then bvdMask w else (x `div` y) .&. bvdMask w
bvSDiv w x y
  | y == 0 = bvdMask w
  | otherwise =
      let widthInt = fromIntegral (natValue w) :: Int
          half = bit (widthInt - 1)
          x_signed = if x >= half then x - bit widthInt else x
          y_signed = if y >= half then y - bit widthInt else y
          result = x_signed `div` y_signed
       in result .&. bvdMask w
bvURem w x y = if y == 0 then x else (x `mod` y) .&. bvdMask w
bvSRem w x y
  | y == 0 = x
  | otherwise =
      let widthInt = fromIntegral (natValue w) :: Int
          half = bit (widthInt - 1)
          x_signed = if x >= half then x - bit widthInt else x
          y_signed = if y >= half then y - bit widthInt else y
          result = x_signed `mod` y_signed
       in result .&. bvdMask w

bvAnd, bvOr, bvXor :: Integer -> Integer -> Integer
bvAnd = (.&.)
bvOr = (.|.)
bvXor = Bits.xor

bvNot :: NatRepr w -> Integer -> Integer
bvNot w x = complement x .&. bvdMask w

bvShl, bvLShr, bvAShr :: NatRepr w -> Integer -> Integer -> Integer
bvShl w x k = (x `shiftL` fromIntegral k) .&. bvdMask w
bvLShr w x k = (x `shiftR` fromIntegral k) .&. bvdMask w
bvAShr w x k =
  let widthInt = fromIntegral (natValue w) :: Int
      half = bit (widthInt - 1)
      x_signed = if x >= half then x - bit widthInt else x
      result = x_signed `shiftR` fromIntegral k
   in result .&. bvdMask w

-- | Correctness: singleton contains exactly the given value
correct_singleton :: (1 <= w) => NatRepr w -> Integer -> Property
correct_singleton w x =
  let x' = x .&. bvdMask w
      swb = singleton w x'
   in property $ member swb x'

-- | Correctness: member test is sound
correct_member :: (SWB w, Integer) -> Property
correct_member (swb, val) =
  property $ member swb val

-- | Correctness: fromRange is sound
correct_from_range :: (1 <= w) => NatRepr w -> Integer -> Integer -> Integer -> Property
correct_from_range w lo hi x =
  let lo' = lo .&. bvdMask w
      hi' = hi .&. bvdMask w
      x' = x .&. bvdMask w
      swb = fromRange w lo' hi'
      -- x is in range if it's between lo and hi (wrapping considered)
      inRange = if lo' <= hi'
                then lo' <= x' && x' <= hi'
                else lo' <= x' || x' <= hi'
   in property $ if inRange then member swb x' else True

-- | Correctness: reduce is idempotent
correct_reduce_idempotent :: (1 <= w) => SWB w -> Property
correct_reduce_idempotent swb =
  property $ reduce (reduce swb) == reduce swb

-- | Correctness: join is sound
correct_join :: (1 <= w) => (SWB w, Integer) -> (SWB w, Integer) -> Property
correct_join (swb1, x) (swb2, y) =
  property $
    member (join swb1 swb2) x &&
    member (join swb1 swb2) y

-- | Correctness: meet is sound
correct_meet :: (1 <= w) => (SWB w, Integer) -> (SWB w, Integer) -> Property
correct_meet (swb1, x) (swb2, y) =
  let m = meet swb1 swb2
   in property $ if x == y then member m x else True

-- | Correctness: le is sound
correct_le :: (SWB w, Integer) -> (SWB w, Integer) -> Property
correct_le (swb1, x) (swb2, _) =
  property $ if le swb1 swb2 then member swb2 x else True

-- | Correctness: addition is sound
correct_add :: (1 <= w) => (SWB w, Integer) -> (SWB w, Integer) -> Property
correct_add (swb1, x) (swb2, y) =
  let w = swbWidth swb1
      result = add swb1 swb2
   in property $ member result (bvAdd w x y)

-- | Correctness: negation is sound
correct_neg :: (1 <= w) => (SWB w, Integer) -> Property
correct_neg (swb, x) =
  let w = swbWidth swb
      result = neg swb
   in property $ member result (bvSub w 0 x)

-- | Correctness: subtraction is sound
correct_sub :: (1 <= w) => (SWB w, Integer) -> (SWB w, Integer) -> Property
correct_sub (swb1, x) (swb2, y) =
  let w = swbWidth swb1
      result = sub swb1 swb2
   in property $ member result (bvSub w x y)

-- | Correctness: multiplication is sound
correct_mul :: (1 <= w) => (SWB w, Integer) -> (SWB w, Integer) -> Property
correct_mul (swb1, x) (swb2, y) =
  let w = swbWidth swb1
      result = mul swb1 swb2
   in property $ member result (bvMul w x y)

-- | Correctness: AND is sound
correct_and :: (1 <= w) => (SWB w, Integer) -> (SWB w, Integer) -> Property
correct_and (swb1, x) (swb2, y) =
  property $ member (and swb1 swb2) (bvAnd x y)

-- | Correctness: OR is sound
correct_or :: (1 <= w) => (SWB w, Integer) -> (SWB w, Integer) -> Property
correct_or (swb1, x) (swb2, y) =
  property $ member (or swb1 swb2) (bvOr x y)

-- | Correctness: XOR is sound
correct_xor :: (1 <= w) => (SWB w, Integer) -> (SWB w, Integer) -> Property
correct_xor (swb1, x) (swb2, y) =
  property $ member (xor swb1 swb2) (bvXor x y)

-- | Correctness: NOT is sound
correct_not :: (1 <= w) => (SWB w, Integer) -> Property
correct_not (swb, x) =
  let w = swbWidth swb
   in property $ member (not swb) (bvNot w x)

-- | Correctness: left shift is sound
correct_shl :: (1 <= w) => (SWB w, Integer) -> Integer -> Property
correct_shl (swb, x) k =
  let w = swbWidth swb
   in property $ member (shl swb k) (bvShl w x k)

-- | Correctness: logical right shift is sound
correct_lshr :: (1 <= w) => (SWB w, Integer) -> Integer -> Property
correct_lshr (swb, x) k =
  let w = swbWidth swb
   in property $ member (lshr swb k) (bvLShr w x k)

-- | Correctness: arithmetic right shift is sound
correct_ashr :: (1 <= w) => (SWB w, Integer) -> Integer -> Property
correct_ashr (swb, x) k =
  let w = swbWidth swb
   in property $ member (ashr swb k) (bvAShr w x k)

--------------------------------------------------------------------------------
-- Lattice properties

-- | Lattice property: join is commutative
lattice_join_commutative :: (1 <= w) => SWB w -> SWB w -> Property
lattice_join_commutative x y =
  property $ join x y == join y x

-- | Lattice property: meet is commutative
lattice_meet_commutative :: (1 <= w) => SWB w -> SWB w -> Property
lattice_meet_commutative x y =
  property $ meet x y == meet y x

-- | Lattice property: join is associative
lattice_join_associative :: (1 <= w) => SWB w -> SWB w -> SWB w -> Property
lattice_join_associative x y z =
  property $ join (join x y) z == join x (join y z)

-- | Lattice property: meet is associative
lattice_meet_associative :: (1 <= w) => SWB w -> SWB w -> SWB w -> Property
lattice_meet_associative x y z =
  property $ meet (meet x y) z == meet x (meet y z)

-- | Lattice property: join is idempotent
lattice_join_idempotent :: (1 <= w) => SWB w -> Property
lattice_join_idempotent x =
  property $ join x x == x

-- | Lattice property: meet is idempotent
lattice_meet_idempotent :: (1 <= w) => SWB w -> Property
lattice_meet_idempotent x =
  property $ meet x x == x

-- | Lattice property: absorption law 1
lattice_absorption1 :: (1 <= w) => SWB w -> SWB w -> Property
lattice_absorption1 x y =
  property $ join x (meet x y) == x

-- | Lattice property: absorption law 2
lattice_absorption2 :: (1 <= w) => SWB w -> SWB w -> Property
lattice_absorption2 x y =
  property $ meet x (join x y) == x

-- | Lattice property: le is reflexive
lattice_le_reflexive :: SWB w -> Property
lattice_le_reflexive x =
  property $ le x x

-- | Lattice property: le is antisymmetric
lattice_le_antisymmetric :: SWB w -> SWB w -> Property
lattice_le_antisymmetric x y =
  property $ if (le x y && le y x) then (x == y) else True

-- | Lattice property: le is transitive
lattice_le_transitive :: SWB w -> SWB w -> SWB w -> Property
lattice_le_transitive x y z =
  property $ if (le x y && le y z) then le x z else True

-- | Lattice property: join is upper bound 1
lattice_join_upper_bound1 :: (1 <= w) => SWB w -> SWB w -> Property
lattice_join_upper_bound1 x y =
  property $ le x (join x y)

-- | Lattice property: join is upper bound 2
lattice_join_upper_bound2 :: (1 <= w) => SWB w -> SWB w -> Property
lattice_join_upper_bound2 x y =
  property $ le y (join x y)

-- | Lattice property: meet is lower bound 1
lattice_meet_lower_bound1 :: (1 <= w) => SWB w -> SWB w -> Property
lattice_meet_lower_bound1 x y =
  property $ le (meet x y) x

-- | Lattice property: meet is lower bound 2
lattice_meet_lower_bound2 :: (1 <= w) => SWB w -> SWB w -> Property
lattice_meet_lower_bound2 x y =
  property $ le (meet x y) y

-- | Lattice property: join is least upper bound
lattice_join_least_upper_bound :: (1 <= w) => SWB w -> SWB w -> SWB w -> Property
lattice_join_least_upper_bound x y z =
  property $ if (le x z && le y z) then le (join x y) z else True

-- | Lattice property: meet is greatest lower bound
lattice_meet_greatest_lower_bound :: (1 <= w) => SWB w -> SWB w -> SWB w -> Property
lattice_meet_greatest_lower_bound x y z =
  property $ if (le z x && le z y) then le z (meet x y) else True

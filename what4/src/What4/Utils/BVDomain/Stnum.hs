{-|
Module      : What4.Utils.BVDomain.Stnum
Copyright   : (c) Galois Inc, 2025
License     : BSD3
Maintainer  : langston@galois.com

Provides stnum (signedness-aware tnum) abstract domain for bitvectors,
implementing bit-level tracking with signedness awareness.

An stnum extends tnums by splitting the bitvector space at the sign bit (MSB)
into two hemispheres:
- Hemisphere 0: MSB=0 (non-negative values: 0 to 2^(w-1)-1)
- Hemisphere 1: MSB=1 (negative values: 2^(w-1) to 2^w-1)

This signedness-aware representation enables precise tracking of signed/unsigned
semantics and wrapped arithmetic behaviors.

Based on algorithms from:
- Linux eBPF verifier (tnum implementation)
- Clam static analyzer (crab/domains/tnum.hpp, stnum.hpp)
- "Signedness-Agnostic Program Analysis" (ISSTA 2025)

= Implementation Notes

This implementation closely follows the Clam reference (stnum_impl.hpp) with
key improvements:

* __Precise bitwise operations__: The @and@, @or@, and @xor@ operations now
  match the Clam reference (stnum_impl.hpp:1274-1309) instead of using
  conservative over-approximations. These operations correctly track which
  hemisphere (MSB=0 or MSB=1) results belong to based on the input hemispheres:

  - AND produces MSB=1 only when both inputs have MSB=1
  - OR produces MSB=0 only when both inputs have MSB=0
  - XOR produces MSB=0 when inputs have the same MSB, MSB=1 when different

* __Hemisphere normalization__: The @normalize@ function properly handles the
  conversion of single tnums to stnums by splitting them into hemispheres
  using @getZeroCircle@ and @getOneCircle@.

* __Exact algorithm match__: Arithmetic operations precisely match the Clam
  reference for maximum correctness.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module What4.Utils.BVDomain.Stnum
  ( -- * Tnum type (re-exported)
    Tnum(TnumBottom, TnumValue)
    -- * Stnum type
  , Stnum(..)
  , bottom, top, singleton
  , isBottom, member, proper
  , width
    -- * Stnum hemisphere operations
  , normalize
    -- * Stnum lattice operations
  , join, meet, le
    -- * Stnum arithmetic operations
  , add, neg, sub, mul
  , udiv, sdiv, urem, srem
    -- * Stnum bitwise operations
  , and, or, xor, not
    -- * Stnum shift operations
  , shl, lshr, ashr
  , shlStnum, lshrStnum, ashrStnum
    -- * Stnum width operations
  , zext, sext, trunc
  , rol, ror
    -- * Stnum comparison operations
  , eq, ult, slt
    -- * Testing support
  , genStnum, genStnumPair
    -- * Correctness properties
  , correct_singleton
  , correct_member
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
  , correct_join
  , correct_meet
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

import           What4.Utils.BVDomain.Tnum (Tnum, pattern TnumBottom, pattern TnumValue)
import qualified What4.Utils.BVDomain.Tnum as Tnum

--------------------------------------------------------------------------------
-- Stnum definition

-- | Stnum (signedness-aware tnum) splits bitvector space at the MSB (sign bit).
--
-- Hemisphere 0: MSB=0 (signed non-negative: 0 to 2^(w-1)-1)
-- Hemisphere 1: MSB=1 (signed negative: 2^(w-1) to 2^w-1)
--
-- This representation enables precise tracking of signed/unsigned semantics
-- and wrapped arithmetic behaviors.

data Stnum (w :: Nat) =
  Stnum
    { stnumHemi0 :: !(Tnum w)  -- ^ Non-negative hemisphere (MSB=0)
    , stnumHemi1 :: !(Tnum w)  -- ^ Negative hemisphere (MSB=1)
    }
  deriving Show

-- | Equality for stnums
instance Eq (Stnum w) where
  Stnum h00 h01 == Stnum h10 h11 = h00 == h10 && h01 == h11

--------------------------------------------------------------------------------
-- Stnum basic operations

-- | Get the width witness from an stnum
width :: Stnum w -> NatRepr w
width (Stnum h0 _) = Tnum.width h0

-- | The empty stnum (bottom element)
bottom :: (1 <= w) => NatRepr w -> Stnum w
bottom w = Stnum (Tnum.bottom w) (Tnum.bottom w)

-- | The universal stnum representing all bitvectors
top :: (1 <= w) => NatRepr w -> Stnum w
top w =
  let widthInt = fromIntegral (natValue w) :: Int
      hemi0 = Tnum.fromRange w 0 (bit (widthInt - 1) - 1)
      hemi1 = Tnum.fromRange w (bit (widthInt - 1)) (Tnum.bvdMask w)
   in Stnum hemi0 hemi1

-- | Create an stnum representing a single value
singleton :: (1 <= w) => NatRepr w -> Integer -> Stnum w
singleton w x =
  let widthInt = fromIntegral (natValue w) :: Int
      msb = Bits.testBit x (widthInt - 1)
   in if msb
      then Stnum (Tnum.bottom w) (Tnum.singleton w x)
      else Stnum (Tnum.singleton w x) (Tnum.bottom w)

-- | Test if an stnum is bottom (empty set)
isBottom :: Stnum w -> Bool
isBottom (Stnum h0 h1) = Tnum.isBottom h0 && Tnum.isBottom h1

-- | Test if a concrete value is a member of an stnum
member :: Stnum w -> Integer -> Bool
member (Stnum h0 h1) x =
  Tnum.member h0 x || Tnum.member h1 x

-- | Check if an stnum satisfies its representation invariants
proper :: Stnum w -> Bool
proper (Stnum h0 h1) = Tnum.proper h0 && Tnum.proper h1

--------------------------------------------------------------------------------
-- Stnum hemisphere operations

-- | Normalize a pair of tnums into an stnum.
--
-- This is the "split" operation from the paper: it takes two arbitrary
-- tnums and splits them into hemispheres, then joins the results.
normalize :: (1 <= w) => Tnum w -> Tnum w -> Stnum w
normalize t0 t1
  | Tnum.isBottom t0 && Tnum.isBottom t1 =
      bottom (Tnum.width t0)
  | Tnum.isTop t0 || Tnum.isTop t1 =
      top (Tnum.width t0)
  | Tnum.isBottom t0 && Prelude.not (Tnum.isBottom t1) =
      let (zero, one) = Tnum.getCircles t1
       in Stnum zero one
  | Prelude.not (Tnum.isBottom t0) && Tnum.isBottom t1 =
      let (zero, one) = Tnum.getCircles t0
       in Stnum zero one
  | otherwise =
      let (z0, o0) = Tnum.getCircles t0
          (z1, o1) = Tnum.getCircles t1
       in Stnum (Tnum.join z0 z1) (Tnum.join o0 o1)

--------------------------------------------------------------------------------
-- Stnum lattice operations

-- | Lattice join for stnums.
--
-- Joins each hemisphere independently.
join :: (1 <= w) => Stnum w -> Stnum w -> Stnum w
join (Stnum h00 h01) (Stnum h10 h11) =
  Stnum (Tnum.join h00 h10) (Tnum.join h01 h11)

-- | Lattice meet for stnums.
--
-- Meets each hemisphere independently.
meet :: (1 <= w) => Stnum w -> Stnum w -> Stnum w
meet (Stnum h00 h01) (Stnum h10 h11) =
  Stnum (Tnum.meet h00 h10) (Tnum.meet h01 h11)

-- | Subsumption test for stnums.
--
-- s1 <= s2 iff each hemisphere of s1 is subsumed by the corresponding hemisphere of s2.
le :: Stnum w -> Stnum w -> Bool
le (Stnum h00 h01) (Stnum h10 h11) =
  Tnum.le h00 h10 && Tnum.le h01 h11

--------------------------------------------------------------------------------
-- Stnum arithmetic operations

-- | Stnum addition.
--
-- Pattern: apply tnum operation to all hemisphere combinations, then normalize.
add :: (1 <= w) => Stnum w -> Stnum w -> Stnum w
add (Stnum h00 h01) (Stnum h10 h11) =
  let t00 = Tnum.add h00 h10  -- hemi0 + hemi0
      t01 = Tnum.add h00 h11  -- hemi0 + hemi1
      t10 = Tnum.add h01 h10  -- hemi1 + hemi0
      t11 = Tnum.add h01 h11  -- hemi1 + hemi1
      sameHemi = normalize t00 t11
      diffHemi = normalize t01 t10
   in join sameHemi diffHemi

-- | Stnum negation.
neg :: (1 <= w) => Stnum w -> Stnum w
neg (Stnum h0 h1) =
  let t0 = Tnum.neg h0
      t1 = Tnum.neg h1
   in normalize t0 t1

-- | Stnum subtraction.
sub :: (1 <= w) => Stnum w -> Stnum w -> Stnum w
sub s1 s2 = add s1 (neg s2)

-- | Stnum multiplication.
--
-- Results are grouped by sign (which hemisphere they belong to):
-- - t00 (pos×pos=pos) and t11 (neg×neg=pos) → hemisphere 0 (non-negative)
-- - t01 (pos×neg=neg) and t10 (neg×pos=neg) → hemisphere 1 (negative)
--
-- Matches Clam stnum_impl.hpp:1073
mul :: (1 <= w) => Stnum w -> Stnum w -> Stnum w
mul (Stnum h00 h01) (Stnum h10 h11) =
  let t00 = Tnum.mul h00 h10  -- pos × pos = pos
      t01 = Tnum.mul h00 h11  -- pos × neg = neg
      t10 = Tnum.mul h01 h10  -- neg × pos = neg
      t11 = Tnum.mul h01 h11  -- neg × neg = pos
   in normalize (Tnum.join t00 t11) (Tnum.join t01 t10)

-- | Stnum division/remainder operations.
--
-- Apply tnum operation to all hemisphere combinations, then normalize.
udiv :: (1 <= w) => Stnum w -> Stnum w -> Stnum w
udiv (Stnum h00 h01) (Stnum h10 h11) =
  let t00 = Tnum.udiv h00 h10
      t01 = Tnum.udiv h00 h11
      t10 = Tnum.udiv h01 h10
      t11 = Tnum.udiv h01 h11
   in normalize (Tnum.join t00 t01) (Tnum.join t10 t11)

sdiv :: (1 <= w) => Stnum w -> Stnum w -> Stnum w
sdiv (Stnum h00 h01) (Stnum h10 h11) =
  let t00 = Tnum.sdiv h00 h10
      t01 = Tnum.sdiv h00 h11
      t10 = Tnum.sdiv h01 h10
      t11 = Tnum.sdiv h01 h11
   in normalize (Tnum.join t00 t01) (Tnum.join t10 t11)

urem :: (1 <= w) => Stnum w -> Stnum w -> Stnum w
urem (Stnum h00 h01) (Stnum h10 h11) =
  let t00 = Tnum.urem h00 h10
      t01 = Tnum.urem h00 h11
      t10 = Tnum.urem h01 h10
      t11 = Tnum.urem h01 h11
   in normalize (Tnum.join t00 t01) (Tnum.join t10 t11)

srem :: (1 <= w) => Stnum w -> Stnum w -> Stnum w
srem (Stnum h00 h01) (Stnum h10 h11) =
  let t00 = Tnum.srem h00 h10
      t01 = Tnum.srem h00 h11
      t10 = Tnum.srem h01 h10
      t11 = Tnum.srem h01 h11
   in normalize (Tnum.join t00 t01) (Tnum.join t10 t11)

--------------------------------------------------------------------------------
-- Stnum bitwise operations

-- | Stnum bitwise AND.
--
-- Algorithm from Clam stnum_impl.hpp:1274-1281.
-- AND of two values with MSB=0 or MSB=1 produces:
--   - MSB=0 if at least one input has MSB=0
--   - MSB=1 only if both inputs have MSB=1
and :: (1 <= w) => Stnum w -> Stnum w -> Stnum w
and (Stnum h00 h01) (Stnum h10 h11) =
  let h0' = Tnum.join (Tnum.and h00 h10) (Tnum.join (Tnum.and h00 h11) (Tnum.and h01 h10))
      h1' = Tnum.and h01 h11
   in Stnum h0' h1'

-- | Stnum bitwise OR.
--
-- Algorithm from Clam stnum_impl.hpp:1286-1293.
-- OR of two values with MSB=0 or MSB=1 produces:
--   - MSB=0 only if both inputs have MSB=0
--   - MSB=1 if at least one input has MSB=1
or :: (1 <= w) => Stnum w -> Stnum w -> Stnum w
or (Stnum h00 h01) (Stnum h10 h11) =
  let h0' = Tnum.or h00 h10
      h1' = Tnum.join (Tnum.or h01 h11) (Tnum.join (Tnum.or h01 h10) (Tnum.or h00 h11))
   in Stnum h0' h1'

-- | Stnum bitwise XOR.
xor :: (1 <= w) => Stnum w -> Stnum w -> Stnum w
xor (Stnum h00 h01) (Stnum h10 h11) =
  let t00 = Tnum.xor h00 h10  -- Both MSB=0, result MSB=0
      t01 = Tnum.xor h00 h11  -- MSB differ, result MSB=1
      t10 = Tnum.xor h01 h10  -- MSB differ, result MSB=1
      t11 = Tnum.xor h01 h11  -- Both MSB=1, result MSB=0
   in Stnum (Tnum.join t00 t11) (Tnum.join t01 t10)

-- | Stnum bitwise NOT.
not :: (1 <= w) => Stnum w -> Stnum w
not (Stnum h0 h1) =
  -- NOT flips the MSB, so hemisphere 0 goes to hemisphere 1 and vice versa
  Stnum (Tnum.not h1) (Tnum.not h0)

--------------------------------------------------------------------------------
-- Stnum shift operations

-- | Stnum left shift.
shl :: (1 <= w) => Stnum w -> Integer -> Stnum w
shl (Stnum h0 h1) k =
  let t0 = Tnum.shl h0 k
      t1 = Tnum.shl h1 k
   in normalize t0 t1

-- | Stnum logical right shift.
lshr :: (1 <= w) => Stnum w -> Integer -> Stnum w
lshr (Stnum h0 h1) k =
  let t0 = Tnum.lshr h0 k
      t1 = Tnum.lshr h1 k
   in normalize t0 t1

-- | Stnum arithmetic right shift.
ashr :: (1 <= w) => Stnum w -> Integer -> Stnum w
ashr (Stnum h0 h1) k =
  -- Hemisphere 0 (MSB=0): logical shift (stays in hemisphere 0)
  -- Hemisphere 1 (MSB=1): arithmetic shift (stays in hemisphere 1 due to sign extension)
  Stnum (Tnum.lshr h0 k) (Tnum.ashr h1 k)

-- | Stnum left shift by stnum (non-constant shift amount).
--
-- If shift amount is only in hemisphere 0, avoid normalizing for better precision.
-- Based on Clam stnum_impl.hpp:1224-1241.
shlStnum :: (1 <= w) => Stnum w -> Stnum w -> Stnum w
shlStnum s1@(Stnum h00 h01) s2@(Stnum h10 h11)
  | isBottom s1 || isBottom s2 = bottom (width s1)
  | Tnum.isBottom h11 =
      -- Shift amount only in hemisphere 0 (non-negative), more precise
      -- Don't normalize since shifts stay in reasonable range
      Stnum (Tnum.shlTnum h00 h10) (Tnum.shlTnum h01 h10)
  | otherwise =
      -- Shift amount could be large (hemisphere 1), return top
      top (width s1)

-- | Stnum logical right shift by stnum (non-constant shift amount).
--
-- Based on Clam stnum_impl.hpp:1243-1259.
lshrStnum :: (1 <= w) => Stnum w -> Stnum w -> Stnum w
lshrStnum s1@(Stnum h00 h01) s2@(Stnum h10 h11)
  | isBottom s1 || isBottom s2 = bottom (width s1)
  | Tnum.isBottom h11 =
      -- Shift amount only in hemisphere 0
      Stnum (Tnum.lshrTnum h00 h10) (Tnum.lshrTnum h01 h10)
  | otherwise =
      -- Shift amount could be large
      top (width s1)

-- | Stnum arithmetic right shift by stnum (non-constant shift amount).
--
-- Based on Clam stnum_impl.hpp:1261-1277.
ashrStnum :: (1 <= w) => Stnum w -> Stnum w -> Stnum w
ashrStnum s1@(Stnum h00 h01) s2@(Stnum h10 h11)
  | isBottom s1 || isBottom s2 = bottom (width s1)
  | Tnum.isBottom h11 =
      -- Shift amount only in hemisphere 0
      -- h0 stays non-negative, h1 stays negative
      Stnum (Tnum.lshrTnum h00 h10) (Tnum.ashrTnum h01 h10)
  | otherwise =
      -- Shift amount could be large
      top (width s1)

--------------------------------------------------------------------------------
-- Stnum width operations

-- | Stnum zero extension (placeholder - needs width operations on tnum first).
zext :: (1 <= w, w+1 <= u) => Stnum w -> NatRepr u -> Stnum u
zext (Stnum h0 h1) u =
  Stnum (Tnum.zext h0 u) (Tnum.zext h1 u)

-- | Stnum sign extension (placeholder - needs width operations on tnum first).
sext :: (1 <= w, 1 <= u, w+1 <= u) => Stnum w -> NatRepr u -> Stnum u
sext (Stnum h0 h1) u =
  -- Hemisphere 0 (non-negative): zero extend
  -- Hemisphere 1 (negative): sign extend
  Stnum (Tnum.zext h0 u) (Tnum.sext h1 u)

-- | Stnum truncation (placeholder - needs width operations on tnum first).
trunc :: (1 <= n, n+1 <= w) => NatRepr n -> Stnum w -> Stnum n
trunc n (Stnum h0 h1) =
  let t0 = Tnum.trunc n h0
      t1 = Tnum.trunc n h1
   in normalize t0 t1

-- | Stnum rotate left (placeholder - needs rotations on tnum first).
rol :: (1 <= w) => Stnum w -> Integer -> Stnum w
rol (Stnum h0 h1) k =
  let t0 = Tnum.rol h0 k
      t1 = Tnum.rol h1 k
   in normalize t0 t1

-- | Stnum rotate right (placeholder - needs rotations on tnum first).
ror :: (1 <= w) => Stnum w -> Integer -> Stnum w
ror (Stnum h0 h1) k =
  let t0 = Tnum.ror h0 k
      t1 = Tnum.ror h1 k
   in normalize t0 t1

--------------------------------------------------------------------------------
-- Stnum bounds extraction

-- | Get signed maximum value from stnum.
getSignedMax :: (1 <= w) => Stnum w -> Integer
getSignedMax (Stnum h0 h1)
  | Prelude.not (Tnum.isBottom h0) =
      -- Hemisphere 0 contains non-negative values, so its max is the signed max
      let (TnumValue _ v m) = h0 in v + m
  | Prelude.not (Tnum.isBottom h1) =
      -- Only hemisphere 1, get its max
      let (TnumValue _ v m) = h1 in v + m
  | otherwise = error "getSignedMax: called on bottom"

-- | Get signed minimum value from stnum.
getSignedMin :: (1 <= w) => Stnum w -> Integer
getSignedMin (Stnum h0 h1)
  | Prelude.not (Tnum.isBottom h1) =
      -- Hemisphere 1 contains negative values, so its min (value) is the signed min
      let (TnumValue _ v _) = h1 in v
  | Prelude.not (Tnum.isBottom h0) =
      -- Only hemisphere 0, get its min
      let (TnumValue _ v _) = h0 in v
  | otherwise = error "getSignedMin: called on bottom"

-- | Get unsigned maximum value from stnum.
getUnsignedMax :: (1 <= w) => Stnum w -> Integer
getUnsignedMax (Stnum h0 h1)
  | Prelude.not (Tnum.isBottom h1) =
      -- Hemisphere 1 has larger unsigned values (MSB=1)
      let (TnumValue _ v m) = h1 in v + m
  | Prelude.not (Tnum.isBottom h0) =
      -- Only hemisphere 0
      let (TnumValue _ v m) = h0 in v + m
  | otherwise = error "getUnsignedMax: called on bottom"

-- | Get unsigned minimum value from stnum.
getUnsignedMin :: (1 <= w) => Stnum w -> Integer
getUnsignedMin (Stnum h0 h1)
  | Prelude.not (Tnum.isBottom h0) =
      -- Hemisphere 0 has smaller unsigned values (MSB=0)
      let (TnumValue _ v _) = h0 in v
  | Prelude.not (Tnum.isBottom h1) =
      -- Only hemisphere 1
      let (TnumValue _ v _) = h1 in v
  | otherwise = error "getUnsignedMin: called on bottom"

--------------------------------------------------------------------------------
-- Stnum refinement operations (for constraint propagation)

-- | Lower half-line refinement with bound.
--
-- Given y <= x (in the specified signedness), refine y using x's lower bound.
-- This is used in constraint propagation: if we know y <= x and we know x's
-- minimum value, we can tighten y's range to [x_min, y_max].
lowerHalfLine :: (1 <= w) => Stnum w -> Stnum w -> Bool -> Stnum w
lowerHalfLine y x isSigned =
  let w = width y
   in if isBottom y || isBottom x
      then bottom w
      else let widthInt = fromIntegral (natValue w) :: Int
               widthMask = Tnum.bvdMask w
               signedMin = bit (widthInt - 1)
            in if isSigned
          then -- Signed comparison: y_smax >= x_smin, refine to [x_smin, y_smax]
               let xMinSigned = getSignedMin x
                   yMaxSigned = getSignedMax y
                   -- Convert to unsigned for bit-level comparison
                   xMinBits = xMinSigned .&. widthMask
                   yMaxBits = yMaxSigned .&. widthMask
                   -- Check: (yMax - signedMin) < (xMin - signedMin) means yMax < xMin
                   yMaxOffset = (yMaxBits - signedMin) .&. widthMask
                   xMinOffset = (xMinBits - signedMin) .&. widthMask
                in if yMaxOffset < xMinOffset
                   then bottom w
                   else -- Construct stnum from [xMin, yMax]
                        let xMinMsb = Bits.testBit xMinBits (widthInt - 1)
                            yMaxMsb = Bits.testBit yMaxBits (widthInt - 1)
                         in if xMinMsb == yMaxMsb
                            then -- Both in same hemisphere
                                 let t = Tnum.fromRangeSigned w xMinBits yMaxBits
                                  in if xMinMsb
                                     then Stnum (Tnum.bottom w) t  -- Negative hemisphere
                                     else Stnum t (Tnum.bottom w)  -- Non-negative hemisphere
                            else -- Crosses hemispheres: [xMin, 2^w-1] ∪ [0, yMax]
                                 let tPos = Tnum.fromRangeSigned w 0 yMaxBits
                                     tNeg = Tnum.fromRangeSigned w xMinBits (widthMask)
                                  in Stnum tPos tNeg
          else -- Unsigned comparison: y_umax >= x_umin, refine to [x_umin, y_umax]
               let xMinUnsigned = getUnsignedMin x
                   yMaxUnsigned = getUnsignedMax y
                in if yMaxUnsigned < xMinUnsigned
                   then bottom w
                   else -- Use regular tnum_from_range (unsigned)
                        let t = Tnum.fromRange w xMinUnsigned yMaxUnsigned
                         in normalize t (Tnum.bottom w)

-- | Upper half-line refinement with bound.
--
-- Given y >= x (in the specified signedness), refine y using x's upper bound.
-- This is used in constraint propagation: if we know y >= x and we know x's
-- maximum value, we can tighten y's range to [y_min, x_max].
upperHalfLine :: (1 <= w) => Stnum w -> Stnum w -> Bool -> Stnum w
upperHalfLine y x isSigned =
  let w = width y
   in if isBottom y || isBottom x
      then bottom w
      else let widthInt = fromIntegral (natValue w) :: Int
               widthMask = Tnum.bvdMask w
               signedMin = bit (widthInt - 1)
            in if isSigned
          then -- Signed comparison: y_smin <= x_smax, refine to [y_smin, x_smax]
               let xMaxSigned = getSignedMax x
                   yMinSigned = getSignedMin y
                   -- Convert to unsigned for bit-level comparison
                   xMaxBits = xMaxSigned .&. widthMask
                   yMinBits = yMinSigned .&. widthMask
                   -- Check: (yMin - signedMin) > (xMax - signedMin) means yMin > xMax
                   yMinOffset = (yMinBits - signedMin) .&. widthMask
                   xMaxOffset = (xMaxBits - signedMin) .&. widthMask
                in if yMinOffset > xMaxOffset
                   then bottom w
                   else -- Construct stnum from [yMin, xMax]
                        let yMinMsb = Bits.testBit yMinBits (widthInt - 1)
                            xMaxMsb = Bits.testBit xMaxBits (widthInt - 1)
                         in if yMinMsb == xMaxMsb
                            then -- Both in same hemisphere
                                 let t = Tnum.fromRangeSigned w yMinBits xMaxBits
                                  in if yMinMsb
                                     then Stnum (Tnum.bottom w) t  -- Negative hemisphere
                                     else Stnum t (Tnum.bottom w)  -- Non-negative hemisphere
                            else -- Crosses hemispheres: [yMin, 2^w-1] ∪ [0, xMax]
                                 let tPos = Tnum.fromRangeSigned w 0 xMaxBits
                                     tNeg = Tnum.fromRangeSigned w yMinBits widthMask
                                  in Stnum tPos tNeg
          else -- Unsigned comparison: y_umin <= x_umax, refine to [y_umin, x_umax]
               let xMaxUnsigned = getUnsignedMax x
                   yMinUnsigned = getUnsignedMin y
                in if yMinUnsigned > xMaxUnsigned
                   then bottom w
                   else -- Use regular tnum_from_range (unsigned)
                        let t = Tnum.fromRange w yMinUnsigned xMaxUnsigned
                         in normalize t (Tnum.bottom w)

--------------------------------------------------------------------------------
-- Stnum comparison operations

-- | Stnum equality test.
--
-- Returns Just True if definitely equal, Just False if definitely unequal,
-- Nothing if unknown.
eq :: Stnum w -> Stnum w -> Maybe Bool
eq s1 s2
  | isBottom s1 || isBottom s2 = Nothing
  | s1 == s2 && isSingleton s1 = Just True  -- Both same singleton
  | Prelude.not (stnumOverlap s1 s2) = Just False  -- Disjoint
  | otherwise = Nothing
  where
    isSingleton (Stnum h0 h1) =
      case (Tnum.asSingleton h0, Tnum.asSingleton h1) of
        (Just _, Nothing) -> True
        (Nothing, Just _) -> True
        _ -> False
    stnumOverlap (Stnum h00 h01) (Stnum h10 h11) =
      (Prelude.not (Tnum.isBottom h00) && Prelude.not (Tnum.isBottom h10)) ||
      (Prelude.not (Tnum.isBottom h01) && Prelude.not (Tnum.isBottom h11))

-- | Stnum unsigned less-than (placeholder - needs proper implementation).
ult :: (1 <= w) => Stnum w -> Stnum w -> Maybe Bool
ult _ _ = Nothing  -- Conservative

-- | Stnum signed less-than (placeholder - needs proper implementation).
slt :: (1 <= w) => Stnum w -> Stnum w -> Maybe Bool
slt _ _ = Nothing  -- Conservative

--------------------------------------------------------------------------------
-- Correctness properties

-- | Soundness property: singleton stnum contains the given value
correct_singleton :: (1 <= w) => NatRepr w -> Integer -> Property
correct_singleton w x =
  property $ member (singleton w x) x

-- | Soundness property: stnum membership test is sound
correct_member :: (1 <= w) => (Stnum w, Integer) -> Property
correct_member (s, x) =
  property $ member s x

-- | Soundness property for stnum addition
correct_add :: (1 <= w) => (Stnum w, Integer) -> (Stnum w, Integer) -> Property
correct_add (s1, x) (s2, y) =
  let w = width s1
      mask = Tnum.bvdMask w
   in property $ member (add s1 s2) ((x + y) .&. mask)

-- | Soundness property for stnum negation
correct_neg :: (1 <= w) => (Stnum w, Integer) -> Property
correct_neg (s, x) =
  let w = width s
      mask = Tnum.bvdMask w
   in property $ member (neg s) ((Prelude.negate x) .&. mask)

-- | Soundness property for stnum subtraction
correct_sub :: (1 <= w) => (Stnum w, Integer) -> (Stnum w, Integer) -> Property
correct_sub (s1, x) (s2, y) =
  let w = width s1
      mask = Tnum.bvdMask w
   in property $ member (sub s1 s2) ((x - y) .&. mask)

-- | Soundness property for stnum multiplication
correct_mul :: (1 <= w) => (Stnum w, Integer) -> (Stnum w, Integer) -> Property
correct_mul (s1, x) (s2, y) =
  let w = width s1
      mask = Tnum.bvdMask w
   in property $ member (mul s1 s2) ((x * y) .&. mask)

-- | Soundness property for stnum bitwise AND
correct_and :: (1 <= w) => (Stnum w, Integer) -> (Stnum w, Integer) -> Property
correct_and (s1, x) (s2, y) =
  property $ member (and s1 s2) (x .&. y)

-- | Soundness property for stnum bitwise OR
correct_or :: (1 <= w) => (Stnum w, Integer) -> (Stnum w, Integer) -> Property
correct_or (s1, x) (s2, y) =
  property $ member (or s1 s2) (x .|. y)

-- | Soundness property for stnum bitwise XOR
correct_xor :: (1 <= w) => (Stnum w, Integer) -> (Stnum w, Integer) -> Property
correct_xor (s1, x) (s2, y) =
  let w = width s1
      mask = Tnum.bvdMask w
   in property $ member (xor s1 s2) ((Bits.xor x y) .&. mask)

-- | Soundness property for stnum bitwise NOT
correct_not :: (1 <= w) => (Stnum w, Integer) -> Property
correct_not (s, x) =
  let w = width s
      mask = Tnum.bvdMask w
   in property $ member (not s) ((complement x) .&. mask)

-- | Soundness property for stnum left shift
correct_shl :: (1 <= w) => (Stnum w, Integer) -> Integer -> Property
correct_shl (s, x) k =
  let w = width s
      mask = Tnum.bvdMask w
   in property $ member (shl s k) ((x `shiftL` fromIntegral k) .&. mask)

-- | Soundness property for stnum logical right shift
correct_lshr :: (1 <= w) => (Stnum w, Integer) -> Integer -> Property
correct_lshr (s, x) k =
  property $ member (lshr s k) (x `shiftR` fromIntegral k)

-- | Soundness property for stnum arithmetic right shift
correct_ashr :: (1 <= w) => (Stnum w, Integer) -> Integer -> Property
correct_ashr (s, x) k =
  let w = width s
      widthInt = fromIntegral (natValue w) :: Int
      mask = Tnum.bvdMask w
      -- Convert to signed, shift, convert back
      xs = if Bits.testBit x (widthInt - 1)
           then x - (Bits.bit widthInt)
           else x
      result = (xs `shiftR` fromIntegral k) .&. mask
   in property $ member (ashr s k) result

-- | Soundness property for stnum lattice join
correct_join :: (1 <= w) => (Stnum w, Integer) -> (Stnum w, Integer) -> Property
correct_join (s1, x) (s2, _) =
  -- If x is in s1, it should be in join(s1, s2)
  property $ member (join s1 s2) x

-- | Soundness property for stnum lattice meet
correct_meet :: (1 <= w) => (Stnum w, Integer) -> (Stnum w, Integer) -> Property
correct_meet (s1, x1) (s2, x2) =
  -- If x1 is in s1 AND x1 is in s2, then x1 should be in meet(s1, s2)
  if member s2 x1
  then property $ member (meet s1 s2) x1
  else property True  -- Skip if x1 not in s2

--------------------------------------------------------------------------------
-- Test generators

-- | Generate a random stnum
genStnum :: (1 <= w) => NatRepr w -> Gen (Stnum w)
genStnum w = Stnum <$> Tnum.gen w <*> Tnum.gen w

-- | Generate an stnum and a member of that stnum
-- Never generates bottom (always generates an stnum with at least one member)
genStnumPair :: (1 <= w) => NatRepr w -> Gen (Stnum w, Integer)
genStnumPair w = do
  -- Strategy: generate a single tnum pair (guaranteed non-bottom)
  -- and normalize it to create an stnum
  (t, x) <- Tnum.genPair w

  -- Normalize the tnum into an stnum
  -- This splits it into hemispheres based on the MSB
  let s = normalize t (Tnum.bottom w)

  -- x is guaranteed to be a member of t, and t is now in s
  pure (s, x)

--------------------------------------------------------------------------------
-- Lattice property tests

-- | Join commutativity: join(a, b) = join(b, a)
lattice_join_commutative :: (1 <= w) => Stnum w -> Stnum w -> Property
lattice_join_commutative s1 s2 =
  property $ join s1 s2 == join s2 s1

-- | Meet commutativity: meet(a, b) = meet(b, a)
lattice_meet_commutative :: (1 <= w) => Stnum w -> Stnum w -> Property
lattice_meet_commutative s1 s2 =
  property $ meet s1 s2 == meet s2 s1

-- | Join associativity: join(a, join(b, c)) = join(join(a, b), c)
lattice_join_associative :: (1 <= w) => Stnum w -> Stnum w -> Stnum w -> Property
lattice_join_associative s1 s2 s3 =
  property $ join s1 (join s2 s3) == join (join s1 s2) s3

-- | Meet associativity: meet(a, meet(b, c)) = meet(meet(a, b), c)
lattice_meet_associative :: (1 <= w) => Stnum w -> Stnum w -> Stnum w -> Property
lattice_meet_associative s1 s2 s3 =
  property $ meet s1 (meet s2 s3) == meet (meet s1 s2) s3

-- | Join idempotence: join(a, a) = a
lattice_join_idempotent :: (1 <= w) => Stnum w -> Property
lattice_join_idempotent s =
  property $ join s s == s

-- | Meet idempotence: meet(a, a) = a
lattice_meet_idempotent :: (1 <= w) => Stnum w -> Property
lattice_meet_idempotent s =
  property $ meet s s == s

-- | Absorption law 1: join(a, meet(a, b)) = a
lattice_absorption1 :: (1 <= w) => Stnum w -> Stnum w -> Property
lattice_absorption1 s1 s2 =
  property $ join s1 (meet s1 s2) == s1

-- | Absorption law 2: meet(a, join(a, b)) = a
lattice_absorption2 :: (1 <= w) => Stnum w -> Stnum w -> Property
lattice_absorption2 s1 s2 =
  property $ meet s1 (join s1 s2) == s1

-- | LE reflexivity: a <= a
lattice_le_reflexive :: (1 <= w) => Stnum w -> Property
lattice_le_reflexive s =
  property $ s `le` s

-- | LE antisymmetry: if a <= b and b <= a then a = b
lattice_le_antisymmetric :: (1 <= w) => Stnum w -> Stnum w -> Property
lattice_le_antisymmetric s1 s2 =
  property $ if s1 `le` s2 && s2 `le` s1 then s1 == s2 else True

-- | LE transitivity: if a <= b and b <= c then a <= c
lattice_le_transitive :: (1 <= w) => Stnum w -> Stnum w -> Stnum w -> Property
lattice_le_transitive s1 s2 s3 =
  property $ if s1 `le` s2 && s2 `le` s3 then s1 `le` s3 else True

-- | Join is upper bound: a <= join(a, b)
lattice_join_upper_bound1 :: (1 <= w) => Stnum w -> Stnum w -> Property
lattice_join_upper_bound1 s1 s2 =
  property $ s1 `le` join s1 s2

-- | Join is upper bound: b <= join(a, b)
lattice_join_upper_bound2 :: (1 <= w) => Stnum w -> Stnum w -> Property
lattice_join_upper_bound2 s1 s2 =
  property $ s2 `le` join s1 s2

-- | Meet is lower bound: meet(a, b) <= a
lattice_meet_lower_bound1 :: (1 <= w) => Stnum w -> Stnum w -> Property
lattice_meet_lower_bound1 s1 s2 =
  property $ meet s1 s2 `le` s1

-- | Meet is lower bound: meet(a, b) <= b
lattice_meet_lower_bound2 :: (1 <= w) => Stnum w -> Stnum w -> Property
lattice_meet_lower_bound2 s1 s2 =
  property $ meet s1 s2 `le` s2

-- | Join is least upper bound: if a <= c and b <= c then join(a,b) <= c
lattice_join_least_upper_bound :: (1 <= w) => Stnum w -> Stnum w -> Stnum w -> Property
lattice_join_least_upper_bound s1 s2 s3 =
  property $ if s1 `le` s3 && s2 `le` s3 then join s1 s2 `le` s3 else True

-- | Meet is greatest lower bound: if c <= a and c <= b then c <= meet(a,b)
lattice_meet_greatest_lower_bound :: (1 <= w) => Stnum w -> Stnum w -> Stnum w -> Property
lattice_meet_greatest_lower_bound s1 s2 s3 =
  property $ if s3 `le` s1 && s3 `le` s2 then s3 `le` meet s1 s2 else True

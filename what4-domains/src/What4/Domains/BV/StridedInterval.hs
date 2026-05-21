{-|
Module      : What4.Domains.BV.StridedInterval
Copyright   : (c) Galois, Inc 2026
License     : BSD3
Maintainer  : langston@galois.com

A strided interval domain @{ (base + i * stride) mod 2^w | 0 <= i <= range }@
over fixed-width bitvectors. The empty set is encoded by @stride = 0@
(see 'StridedInterval').

== Visualization

The diagrams below show the represented set as one cell per bitvector
value across @[0, 2^w)@; @*@ marks a member, @.@ a non-member. The
outer brackets are the modulus boundary - values fall off the right
end and reappear on the left.

At @w = 4@:

@
[****************]   'top' (the full set)
[................]   'bottom' (the empty set)
[..*****.........]   stride 1, base 2,  range 4: {2,3,4,5,6}
[..*.*.*.*.......]   stride 2, base 2,  range 3: {2,4,6,8}
[*...*...*...*...]   stride 4, base 0,  range 3: {0,4,8,12}
[**............**]   stride 1, base 14, range 3: {14,15,0,1}   (wraps)
[*...........*.*.]   stride 2, base 12, range 2: {12,14,0}     (wraps)
@

== Width invariant

Every public 'StridedInterval' is /proper/. The empty case is encoded by
@stride = 0@ (with @base = 0@ and @range = 0@). The non-empty case
satisfies

* @0 <= base < 2^w@,
* @stride >= 1@,
* @range >= 0@,
* @(range + 1) * stride <= 2^w@ (the /size cap/), and
* @range == 0@ implies @stride == 1@ (singletons are canonical).

Note that this admits intervals that wrap modulo @2^w@: for @w = 8@, the SI
@base = 250, range = 3, stride = 2@ represents @{250, 252, 254, 0}@.

=== Why the size cap?

The size cap @(range + 1) * stride <= 2^w@ is a /sufficient/ condition for
the @range + 1@ residues @(base + i * stride) mod 2^w@ to be pairwise
distinct: if @0 <= i < j <= range@, then @(j - i) * stride@ lies in
@(0, 2^w)@ and so cannot be a multiple of @2^w@.

It is /not the tightest/ such bound - that would be
@range + 1 <= 2^w \/ gcd(stride, 2^w)@ - but the size-cap form is simpler:
it makes 'member' a single mod-then-divide check, makes 'size' literally
@range + 1@, and lets every operation post-check the result without any
@gcd(_, 2^w)@ bookkeeping. The shapes excluded by the cap (large stride
combined with @range@ near @2^w@) cover almost all of @[0, 2^w)@ and the
sound move for them is 'top' anyway. The bvdomain test suite has algebraic
justifications under @correct_size_cap_*@.

The invariant is checked by 'proper' and verified as a postcondition of
every operation by the @correct_proper_*@ properties below.

== Comparison to "What4.Domains.BV.Arith"

Both modules implement an /interval/ abstract domain over fixed-width
bitvectors with native support for wrapping intervals. The key difference
is that "What4.Domains.BV.Arith" represents only contiguous (stride-1)
intervals, while this module also supports non-trivial strides.

Concretely:

* On stride-1 intervals, the two domains represent exactly the same sets
  and 'join'\/'add'\/'mul'\/etc.\ produce results that round-trip
  identically. Internally, the stride-1 paths in this module delegate to
  "What4.Domains.BV.Arith" so this is true /by construction/, and the
  differential test suite asserts it on every shared operation.

* On strided sets - e.g. @{0, 4, 8, 12}@ at @w = 8@ - only this module is
  precise; "What4.Domains.BV.Arith" would over-approximate to the
  contiguous cover @[0, 12]@.

* When a strided result would overflow the size cap, this module
  conservatively falls back to 'top' rather than dropping to a stride-1
  cover. (A future refinement could match Arith's contiguous cover in
  those cases.)

The upshot: this domain matches "What4.Domains.BV.Arith" exactly on
stride-1 inputs, and is strictly more precise when strides are non-trivial.

== Lattice operations and 'glb'

The lattice operations 'top', 'bottom', 'join', 'meet', 'leq' satisfy
the standard lattice laws (proven as 'join_commutative',
'join_idempotent', etc., below) and 'meet' is a sound /over/-approximation
of the intersection: every concrete value in both operands is also in
@meet a b@.

'glb' is a different function - a strided-interval /under/-approximation
of the intersection, exact when one operand is a singleton or both have
matching strides, but generally a strict subset of the true intersection.
Use 'glb' for path-condition refinement (where dropping witnesses is
acceptable but inventing them is not); use 'meet' when you need a sound
lattice meet (where preserving witnesses is required).
-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module What4.Domains.BV.StridedInterval
  ( StridedInterval (..)
    -- * Constructors
  , singleton
  , mkStridedInterval
  , range
  , fromAscEltList
    -- * Predicates
  , proper
  , asSingleton
  , isAny
  , member
  , pmember
  , domainsOverlap
    -- * Destructors
  , toList
  , size
  , ubounds
  , sbounds
  , bitbounds
  , unknowns
    -- * Comparisons
  , eq
  , ult
  , slt
    -- * Lattice operations
  , top
  , bottom
  , isBottom
  , join
  , meet
  , leq
  , unionSingleton
  , glb
    -- * Width manipulation
  , trunc
  , zext
  , sext
  , concat
  , select
  , normalize
    -- * Arithmetic
  , add
  , adc
  , sub
  , negate
  , scale
  , mul
  , udiv
  , urem
  , sdiv
  , srem
  , not
  , and
  , or
  , xor
    -- * Shifts
  , shl
  , lshr
  , ashr
    -- * Rotates
  , rol
  , ror
    -- * Conversion to\/from "What4.Domains.BV.Arith"
  , asArith
  , toArith
  , fromArith
  , viaArith
    -- * Correctness properties

    -- ** Generators
  , genDomain
  , genElement
  , genPair
    -- ** Invariant postconditions
  , correct_proper_bottom
  , correct_proper_top
  , correct_proper_singleton
  , correct_proper_mkStridedInterval
  , correct_proper_range
  , correct_proper_fromAscEltList
  , correct_proper_join
  , correct_proper_unionSingleton
  , correct_proper_glb
  , correct_proper_add
  , correct_proper_adc
  , correct_proper_sub
  , correct_proper_negate
  , correct_proper_scale
  , correct_proper_mul
  , correct_proper_udiv
  , correct_proper_urem
  , correct_proper_sdiv
  , correct_proper_srem
  , correct_proper_not
  , correct_proper_and
  , correct_proper_or
  , correct_proper_xor
  , correct_proper_shl
  , correct_proper_lshr
  , correct_proper_ashr
  , correct_proper_rol
  , correct_proper_ror
  , correct_proper_concat
  , correct_proper_select
  , correct_proper_trunc
  , correct_proper_zext
  , correct_proper_sext
    -- ** Predicates
  , correct_member_toList
  , correct_toList_member
  , correct_asSingleton
  , correct_domainsOverlap
  , correct_domainsOverlap_bottom
    -- ** Lattice operations
  , correct_join
  , correct_meet
  , correct_leq
  , correct_unionSingleton
  , correct_glb
  , correct_glb_singleton_left
  , correct_glb_singleton_right
    -- *** Lattice laws
  , join_commutative
  , join_idempotent
  , meet_commutative
  , meet_idempotent
  , join_top
  , join_bottom
  , meet_top
  , meet_bottom
  , leq_reflexive
  , join_upper_bound
  , join_proper
  , meet_proper
    -- ** Width manipulation
  , correct_concat
  , correct_select
  , correct_trunc
  , correct_zext
  , correct_sext
    -- ** Arithmetic
  , correct_add
  , correct_adc
  , correct_sub
  , correct_negate
  , correct_scale
  , correct_mul
  , correct_udiv
  , correct_urem
  , correct_sdiv
  , correct_srem
  , correct_not
  , correct_and
  , correct_or
  , correct_xor
  , correct_shl
  , correct_lshr
  , correct_ashr
  , correct_rol
  , correct_ror
    -- ** Destructors
  , correct_size
  , correct_ubounds
  , correct_ubounds_bottom
  , correct_sbounds
  , correct_bitbounds
  , correct_unknowns
  , correct_eq
  , correct_ult
  , correct_slt
    -- ** Bottom edge cases
  , correct_glb_bottom_left
  , correct_glb_bottom_right
  , correct_add_bottom_left
  , correct_add_bottom_right
  , correct_mul_bottom_left
  , correct_mul_bottom_right
  ) where

import           Control.Exception (assert)
import qualified Data.Bits as Bits
import qualified Data.Foldable as Fold
import           Data.Parameterized.NatRepr
import           GHC.TypeNats (Nat)
import           Prelude hiding (and, concat, negate, not, or, span)
import qualified Prelude

import qualified What4.Domains.BV.Arith as A
import qualified What4.Domains.BV.Bitwise as B
import           What4.Domains.BV.StridedInterval.Internal
                   (solveLinearDiophantine)
import qualified What4.Domains.Arithmetic as Arith
import           What4.Domains.Verification
                   ( Property, property, (==>), Gen
                   , chooseInt, chooseInteger, getSize
                   )

-- ---------------------------------------------------------------------------
-- Data type and instances

-- | Canonical strided-interval domain element. See module-level haddock
-- for the width invariant; use 'proper' to check it.
--
-- The type parameter @w@ is phantom — the bitvector width is encoded in
-- 'siMask' (which caches @2^w - 1@). This mirrors the design of
-- 'What4.Domains.BV.Arith.Domain'.
--
-- The empty set ('bottom') is encoded by @stride = 0@; the @stride >= 1@
-- invariant on non-empty SIs leaves @stride = 0@ free for this purpose.
-- All other operations should treat @stride = 0@ as a sentinel and not
-- inspect 'base' or 'siRange' on it.
data StridedInterval (w :: Nat) =
  StridedInterval { siMask  :: !Integer   -- ^ Caches @2^w - 1@.
                  , base    :: !Integer
                  , siRange :: !Integer  -- ^ size - 1; only meaningful when @stride > 0@
                  , stride  :: !Integer  -- ^ @0@ encodes empty; otherwise @>= 1@
                  }

instance Eq (StridedInterval w) where
  si1 == si2 =
    base si1 == base si2 &&
    siRange si1 == siRange si2 &&
    stride si1 == stride si2

instance Show (StridedInterval w) where
  show si
    | isBottom si               = "[]"
    | Just s <- asSingleton si = "[" ++ show s ++ "]"
    | otherwise                =
        "[" ++ show (base si) ++
        ", +" ++ show (stride si) ++
        " .. (" ++ show (siRange si + 1) ++ " elts)]"

-- | /O(1)/. Cardinality of the SI; @0@ for empty.
size :: StridedInterval w -> Integer
size si
  | isBottom si = 0
  | otherwise  = siRange si + 1

-- | Modulus @2^w@ at the SI's declared width.
modulus :: StridedInterval w -> Integer
modulus si = siMask si + 1

-- | Check that a mask has the form @2^w - 1@ (all low bits set).
validMask :: Integer -> Bool
validMask mask = mask >= 0 && Arith.isPow2Integer (mask + 1)
{-# INLINE validMask #-}

-- | Mask an integer to unsigned range: @x .&. (2^w - 1)@.
maskUnsigned :: Integer -> Integer -> Integer
maskUnsigned mask x = assert (validMask mask) $ x Bits..&. mask
{-# INLINE maskUnsigned #-}

-- | Interpret a masked integer as a signed value.
maskSigned :: Integer -> Integer -> Integer
maskSigned mask x = assert (validMask mask) $
  let halfMod = (mask + 1) `Bits.shiftR` 1
      xu = x Bits..&. mask
  in if xu Bits..&. halfMod /= 0
     then xu - (mask + 1)
     else xu
{-# INLINE maskSigned #-}

-- | Distance from first to last residue: @range * stride@.
-- Only meaningful on non-empty SIs.
span :: StridedInterval w -> Integer
span si = assert (stride si /= 0) $ siRange si * stride si
{-# INLINE span #-}

-- | Whether the SI's residues fit within one modular cycle without
-- aliasing: @(range + 1) * stride <= 2^w@.
fitsCap :: StridedInterval w -> Bool
fitsCap si = span si + stride si <= modulus si
{-# INLINE fitsCap #-}

-- ---------------------------------------------------------------------------
-- Invariant

-- | /O(1)/. Check the width invariant. See module-level haddock.
proper :: StridedInterval w -> Bool
proper si
  | isBottom si =
      siRange si == 0 && base si == 0 && stride si == 0
  | otherwise =
      stride si >= 1
      && siRange si >= 0
      && 0 <= base si
      && base si <= siMask si
      && fitsCap si
      -- The "full set" is canonicalized to the 'top' shape (base = 0),
      -- so any other base with size m is not proper.
      && Prelude.not (siRange si == siMask si && base si /= 0)
      -- Singletons are canonicalized to stride 1 (the constructor's choice).
      && Prelude.not (siRange si == 0 && stride si /= 1)

-- | /O(1)/. Force a non-canonical interval into the closest canonical
-- overapproximation.
--
-- Operations that build raw intermediates may produce SIs whose base
-- exceeds @m@ or whose span exceeds the modulus. 'normalize' reduces
-- these to proper form, choosing the tightest representable
-- over-approximation when necessary.
--
-- === Cases (4-bit, m = 16)
--
-- __Already fits__ (@(range+1)*stride <= m@): fold @base mod m@, then
-- 'dewrap' if the residues wrap once.
--
-- @
-- input  (base 18, range 2, stride 3):  {18, 21, 24}  ≡ mod 16  {2, 5, 8}
-- output (base  2, range 2, stride 3):  [..*..*..*....]
--                                        0123456789…
-- @
--
-- __Full set__ (@range+1 == m, stride == 1@): collapse to 'top'.
--
-- @
-- input  (base 5, range 15, stride 1):  all 16 values
-- output top
-- @
--
-- __Spans full cycle__ (@range*stride >= m-1@): also 'top'.
--
-- @
-- input  (base 0, range 5, stride 4):   {0,4,8,12,16,20} mod 16 = {0,4,8,12,0,4}
-- output top                            (repeats ⇒ covers everything conservatively)
-- @
--
-- __Cap overflow__ (@(range+1)*stride > m@ but not a full cycle): drop
-- to the contiguous (stride-1) cover of the residues.
--
-- @
-- input  (base 1, range 9, stride 2):   {1,3,5,…,19}  20 values, 10*2 > 16
-- output (base 1, range 18, stride 1):  contiguous cover [1, 19 mod 16] = [1, 3]
--                                        ⇒ wraps: [1..15] ∪ [0..3]
-- @
normalize :: StridedInterval w -> StridedInterval w
normalize si
  | isBottom si = bottom (siMask si)
  | siRange si == 0 = singleton (siMask si) (base si)
  | fitsCap si =
      -- Already fits the size cap. Canonicalize "full set" shapes to
      -- 'top', and fold base mod m for everything else. When the
      -- folded representation wraps the modulus (last residue < first),
      -- try to rotate to a non-wrapping integer-AP representation —
      -- this only succeeds when the sorted residues themselves form
      -- an AP with the same stride.
      if siRange si == siMask si && stride si == 1
        then top (siMask si)
        else dewrap si { base = base si `mod` m }
  | span si >= siMask si = top (siMask si)
  | otherwise =
      -- Cap-overflow: drop to the stride-1 contiguous cover. The set
      -- @{(base + i*stride) mod m | i in [0, range]}@ is contained in
      -- the contiguous interval starting at @base@ with width
      -- @range*stride@.
      StridedInterval { siMask = siMask si
                      , base = base si `mod` m
                      , siRange = span si
                      , stride = 1 }
  where
    m = modulus si

-- | Internal: when an SI's residues form a non-wrapping integer-AP
-- with the same stride after rotation, rewrite the SI in that form.
-- Otherwise leave the wrapping representation alone.
--
-- @
-- input  (base 4, range 3, stride 4):    [....*...*...*...]   {4,8,12,0}   wraps once
-- output (base 0, range 3, stride 4):    [*...*...*...*...]   {0,4,8,12}   non-wrapping
-- @
--
-- This applies when @(range+1)*stride == m@: exactly one residue wraps
-- (the last one), and the wrap distance equals the stride, so the
-- sorted residues form an AP with the same stride starting at
-- @(base - stride) mod m@. The set is unchanged; only the
-- representation rotates.
dewrap :: StridedInterval w -> StridedInterval w
dewrap si
  | span si + stride si == m
  , base si >= stride si =
      si { base = base si - stride si }
  | otherwise = si
  where
    !m = modulus si

-- ---------------------------------------------------------------------------
-- Constructors

-- | /O(1)/. The singleton interval @{v mod 2^w}@. The first argument
-- is the mask @2^w - 1@.
singleton ::
  Integer ->
  Integer ->
  StridedInterval w
singleton mask v = assert (validMask mask) $
  StridedInterval { siMask = mask, base = maskUnsigned mask v, siRange = 0, stride = 1 }

-- | /O(1)/. @range w lo hi@ returns the contiguous (stride-1) interval
-- containing every bitvector formed from the @w@ low order bits of some
-- @i@ in @[lo, hi]@. Mirrors 'What4.Domains.BV.Arith.range'.
range :: NatRepr w -> Integer -> Integer -> StridedInterval w
range w lo hi = fromArith (maxUnsigned w) (A.range w lo hi)

-- | /O(1)/. @mkStridedInterval mask roundUp lo hi s@ constructs the
-- strided interval starting at @lo@, stride @s@, whose largest element
-- is at most @hi@. When @roundUp@ is true the actual upper bound is
-- rounded up to @lo + r * s@ where @r = ceil((hi - lo) / s)@; otherwise
-- it is rounded down. The result is normalized:
-- out-of-range inputs are truncated (possibly to 'top') via 'normalize'.
-- The first argument is the mask @2^w - 1@.
mkStridedInterval ::
  Integer ->
  Bool ->
  Integer ->
  Integer ->
  Integer ->
  StridedInterval w
mkStridedInterval mask roundUp lo hi s = assert (validMask mask) $ assert (s >= 0) go
  where
    go | hi < lo   = bottom mask
       | s == 0    = singleton mask lo
       | r == 0    = singleton mask lo
       | otherwise =
           normalize StridedInterval { siMask = mask, base = lo
                                     , siRange = r, stride = s }
    r | roundUp   = ((hi - lo) + (s - 1)) `div` s
      | otherwise = (hi - lo) `div` s

-- | /O(n * log(2^w)) = O(n * w)/ in the input list length @n@ (each
-- element contributes a gcd update). Build a strided interval covering
-- every element of an ascending, distinct list. Mirrors
-- 'What4.Domains.BV.Arith.fromAscEltList' on stride-1 inputs but
-- preserves the stride when the elements form an arithmetic progression.
fromAscEltList ::
  Fold.Foldable t =>
  NatRepr w ->
  t Integer ->
  StridedInterval w
fromAscEltList w vs =
  -- Accumulate (first, min, max, gcd-of-(v - first)) across all elements.
  -- The stride is the gcd of (v - first); this equals the gcd of (v - lo)
  -- because the Z-module generated by {v_i - x} is invariant under
  -- translation of x.
  case Fold.foldl' step Nothing vs of
    Nothing -> bottom mask
    Just (_first, lo, hi, s) -> mkStridedInterval mask True lo hi s
  where
    mask = maxUnsigned w
    step Nothing v =
      let v' = maskUnsigned mask v
      in Just (v', v', v', 0)
    step (Just (first, lo, hi, g)) v =
      let v' = maskUnsigned mask v
      in Just (first, min lo v', max hi v', gcd g (v' - first))

-- ---------------------------------------------------------------------------
-- Conversion to\/from Arith

-- | /O(1)/. Project a stride-1 SI into a "What4.Domains.BV.Arith"
-- 'A.Domain' /exactly/. Returns 'Nothing' for empty SIs (which Arith
-- cannot represent) and for SIs with stride > 1 (which Arith cannot
-- represent precisely).
--
-- Use this when you need a faithful round-trip; use 'toArith' when you
-- just want a sound contiguous cover.
asArith :: StridedInterval w -> Maybe (A.Domain w)
asArith si
  | isBottom si = Nothing
  | stride si == 1 =
      let !mask = siMask si
      in if siRange si == mask
           then Just (A.BVDAny mask)
           else Just (A.BVDInterval mask (base si) (siRange si))
  | otherwise = Nothing

-- | /O(1)/. Project /any/ SI into a "What4.Domains.BV.Arith" 'A.Domain'.
-- Empty SIs map to 'A.bottom'. For stride > 1 SIs the result is the
-- smallest contiguous cover, a sound over-approximation; for stride-1
-- SIs it is exact (Arith's @BVDInterval@ encoding directly mirrors
-- SI's @base@/@siRange@).
--
-- Use this when handing an SI to an Arith-only operation (e.g. 'udiv').
toArith :: StridedInterval w -> A.Domain w
toArith si
  | isBottom si = A.BVDInterval (siMask si) 0 (-1)
  | otherwise =
      let !mask = siMask si
          !sz   = span si
      in if sz >= mask
           then A.BVDAny mask
           else A.BVDInterval mask (base si) sz

-- | /O(1)/. Lift a "What4.Domains.BV.Arith" domain to a stride-1
-- 'StridedInterval'. Always succeeds. The result represents the same
-- set: 'A.bottom' maps to 'bottom', 'A.top' to 'top', and contiguous
-- intervals to stride-1 SIs.
fromArith :: Integer -> A.Domain w -> StridedInterval w
fromArith mask d = assert (validMask mask) $
  case d of
    _ | A.isBottom d -> bottom mask
    A.BVDAny _ -> top mask
    A.BVDInterval _ lo sz
      | sz >= mask -> top mask
      | otherwise ->
          StridedInterval { siMask = mask
                          , base = lo Bits..&. mask
                          , siRange = sz
                          , stride = 1
                          }

-- | /O(f)/ where @f@ is the cost of the supplied Arith operation. Runs
-- a unary Arith operation on the contiguous cover of an SI. For
-- stride-1 inputs this is exact; for stride > 1 inputs it widens to
-- the 'ubounds' cover (sound over-approximation).
viaArith ::
  NatRepr w ->
  StridedInterval w ->
  (A.Domain w -> A.Domain w) ->
  StridedInterval w
viaArith w si f
  | isBottom si = bottom (maxUnsigned w)
  | otherwise = fromArith (maxUnsigned w) (f (toArith si))

-- ---------------------------------------------------------------------------
-- Predicates

-- | /O(1)/. Returns 'True' if this domain has no members (i.e., is 'bottom').
isBottom :: StridedInterval w -> Bool
isBottom si = stride si == 0

-- | /O(1)/. Returns 'True' if this domain represents every bitvector
-- of width @w@.
isAny :: StridedInterval w -> Bool
isAny si = base si == 0 && siRange si == siMask si && stride si == 1

-- | /O(1)/. @member si x@: true iff @x mod 2^w@ is one of the residues
-- of @si@. Argument order matches 'What4.Domains.BV.Arith.member'.
member :: StridedInterval w -> Integer -> Bool
member si _ | isBottom si = False
member si n =
  let !m = modulus si
      !x = n `mod` m
      !d = (x - base si) `mod` m
      !s = stride si
      !aligned = s == 1 || d `mod` s == 0
  in aligned && d `div` s <= siRange si

-- | /O(1)/. Check that a domain is proper, and that the given value is
-- a member. Mirrors 'What4.Domains.BV.Arith.pmember'.
pmember :: NatRepr w -> StridedInterval w -> Integer -> Bool
pmember _ si x = proper si && member si x

-- | /O(1)/. Return the value if this is a singleton. Mirrors
-- 'What4.Domains.BV.Arith.asSingleton'.
asSingleton :: StridedInterval w -> Maybe Integer
asSingleton si
  | isBottom si = Nothing
  | siRange si == 0 = Just (base si)
  | otherwise = Nothing

-- | /O(w)/. A conservative overlap predicate: returns 'False' only
-- when the residue sets of @a@ and @b@ are provably disjoint. May
-- report 'True' for non-overlapping operands. Always preserves
-- witnesses.
--
-- The cost is /O(log(min(stride a, stride b))) = O(log(2^w)) = O(w)/
-- for the gcd of strides; otherwise /O(1)/.
domainsOverlap ::
  StridedInterval w ->
  StridedInterval w ->
  Bool
domainsOverlap a b
  | isBottom a || isBottom b = False
  | isAny a || isAny b = True
  -- Residue-class disjointness: if @(base a - base b)@ is not a
  -- multiple of @gcd(stride a, stride b)@, no @i@ and @j@ make
  -- @base a + i * stride a = base b + j * stride b@ over the
  -- integers, so the unsigned (non-wrapping) sets are disjoint.
  -- Wrapping operands can still overlap, so this only implies
  -- disjointness when both sets are non-wrapping.
  | g <- gcd (stride a) (stride b)
  , (base a - base b) `mod` g /= 0
  , Prelude.not (wraps a)
  , Prelude.not (wraps b)
  = False
  | otherwise = A.domainsOverlap (toArith a) (toArith b)
  where
    wraps si =
      let !m = modulus si
          !endRes = (base si + span si) `mod` m
      in endRes < base si

-- ---------------------------------------------------------------------------
-- Lattice operations

-- | /O(1)/. Top element of the lattice: represents all bitvectors of width @w@.
-- The argument is the mask @2^w - 1@.
top :: Integer -> StridedInterval w
top mask = assert (validMask mask) $
  StridedInterval { siMask = mask, base = 0, siRange = mask, stride = 1 }
{-# INLINE top #-}

-- | /O(1)/. Bottom element of the lattice: represents the empty set of
-- bitvectors. Encoded as @stride = 0@ (the @stride >= 1@ invariant on
-- non-empty SIs leaves this slot free). The argument is the mask @2^w - 1@.
bottom :: Integer -> StridedInterval w
bottom mask = assert (validMask mask) $
  StridedInterval { siMask = mask, base = 0, siRange = 0, stride = 0 }
{-# INLINE bottom #-}

-- | /O(w)/. Lattice join (least upper bound). Mirrors
-- 'What4.Domains.BV.Arith.join'. On strided inputs, picks
-- representatives whose midpoints are within @2^(w-1)@ of each other
-- (lifting one operand by @2^w@ when not), then takes the
-- gcd-of-strides cover. This matches the wrap-shorter arc that
-- 'A.join' produces for stride-1 inputs.
--
-- @
-- a:       [..***...........]   base 2, range 2, stride 1: {2,3,4}
-- b:       [........***.....]   base 8, range 2, stride 1: {8,9,10}
-- 'join':  [..*********.....]   base 2, range 8, stride 1: {2..10}
-- @
--
-- The cost is /O(log(min(stride si1, stride si2))) = O(log(2^w)) =
-- O(w)/ for the gcd of the operand strides; the rest is /O(1)/.
join ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  StridedInterval w
join s t | isBottom s = t
join s t | isBottom t = s
join si1 si2 =
  -- Twice each interval's midpoint, in the integer representation
  -- (avoids fractions). When the two midpoints are more than 2^(w-1)
  -- apart we lift the smaller-midpoint operand by 2^w to put it on
  -- the "other side" - same trick as 'A.join'.
  let !m = modulus si1
      !ac = 2 * base si1 + span si1
      !bc = 2 * base si2 + span si2
      !b1' = if ac + (m - 1) < bc then base si1 + m else base si1
      !b2' = if bc + (m - 1) < ac then base si2 + m else base si2
      !lower = min b1' b2'
      !upper = max (b1' + span si1)
                   (b2' + span si2)
      -- Singleton inputs have stride = 1 by canonicalization, but that
      -- stride is meaningless (a singleton has only one element). Drop
      -- it from the gcd so the join can pick up the gap stride.
      !s1 = if siRange si1 == 0 then 0 else stride si1
      !s2 = if siRange si2 == 0 then 0 else stride si2
      !gap = max b1' b2' - lower
  in mkStridedInterval (siMask si1) True lower upper
                       (gcd (gcd s1 s2) gap)

-- | /O(w)/. Specialization of 'join' when one operand is a singleton.
-- The new element extends the SI's range by the gap to the nearest
-- endpoint, with the new stride being the gcd of the existing stride
-- and that gap.
--
-- @
-- si:                  [..*.*.*.........]   base 2,  range 2, stride 2: {2,4,6}
-- 's = 10':            [..........*.....]                                {10}
-- 'unionSingleton':    [..*.*.*.*.*.....]   base 2,  range 4, stride 2: {2,4,6,8,10}
-- @
--
-- Picks up the gap stride when it agrees with the existing stride
-- (@gcd(2, 10 - 2) = 2@). When the gap is coprime with the stride,
-- the result drops to stride 1.
--
-- The cost is /O(log(stride si)) = O(log(2^w)) = O(w)/ for the gcd;
-- otherwise /O(1)/.
unionSingleton ::
  (1 <= w) =>
  Integer ->
  StridedInterval w ->
  StridedInterval w
unionSingleton s si
  | isBottom si = singleton (siMask si) s
  | member si s = si
  | Just s' <- asSingleton si =
      let lo = min s s'
          hi = max s s'
      in mkStridedInterval (siMask si) True lo hi (hi - lo)
  | otherwise =
      let !si_upper = base si + span si
      in if s < base si
         then go s si_upper (base si)
         else go (base si) (max s si_upper) s
  where
    go lo hi to_contain =
      mkStridedInterval (siMask si) True lo hi
                        (gcd (stride si) (to_contain - lo))

-- | /O(w)/. Lattice meet: a sound /over/-approximation of the
-- intersection of two domains. For any concrete value @x@, if @x@ is
-- a member of both @a@ and @b@, then @x@ is a member of @meet a b@.
--
-- When @a ⊑ b@ or @b ⊑ a@ the result is the smaller operand exactly
-- (stride preserved). Otherwise routes through 'A.meet' on the
-- contiguous unsigned covers, which gives a stride-1 result.
meet ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  StridedInterval w
meet a _ | isBottom a = a
meet _ b | isBottom b = b
meet a b | isAny a = b
meet a b | isAny b = a
meet a b | a == b = a
meet a b | leq a b = a
meet a b | leq b a = b
meet a b = fromArith (siMask a) (A.meet (toArith a) (toArith b))

-- | /O(w)/. Lattice ordering: @leq si1 si2@ returns 'True' iff every
-- concrete value represented by @si1@ is also represented by @si2@.
--
-- == Algebraic reasoning
--
-- Let @c = (base si1 - base si2) mod m@. Element @i@ of @si1@ lies in
-- @si2@ iff @d_i = (c + i*s1) mod m@ is a multiple of @s2@ in
-- @[0, r2*s2]@. The size cap @(r1+1)*s1 <= m@ implies the AP
-- @c, c+s1, ..., c+r1*s1@ wraps mod @m@ at most once, splitting the
-- indices @[0, r1]@ into a pre-wrap and a post-wrap segment.
--
-- For each segment to lie in @si2@:
--
-- * Its starting offset must be a multiple of @s2@ (residue
--   condition).
-- * If the segment has more than one element, @s2@ must divide @s1@
--   (so consecutive elements stay in the same residue class).
-- * The segment's largest offset must be at most @r2*s2@ (range
--   condition).
--
-- Each check is /O(1)/ in arithmetic; the @gcd@-free formulation runs
-- in /O(w)/ on width-@w@ inputs.
leq ::
  StridedInterval w ->
  StridedInterval w ->
  Bool
leq si1 _ | isBottom si1 = True
leq _ si2 | isBottom si2 = False
leq si1 si2
  | isAny si2 = True
  | Just s <- asSingleton si1 = member si2 s
  | otherwise =
      let !m  = modulus si1
          !s1 = stride si1
          !s2 = stride si2
          !r1 = siRange si1
          !r2 = siRange si2
          !c  = (base si1 - base si2) `mod` m
          -- iWrap: smallest @i >= 1@ such that @c + i*s1 >= m@. Below
          -- @iWrap@ the integer-AP doesn't wrap; at @iWrap@ and beyond it
          -- has wrapped exactly once.
          !iWrap = ((m - c) + s1 - 1) `div` s1
          !wraps = iWrap <= r1
          !preR = if wraps then iWrap - 1 else r1
          !postBase = c + iWrap * s1 - m
          !postR = r1 - iWrap
          -- Check that the integer-AP @{b, b+s1, ..., b + r*s1}@ is wholly
          -- inside @si2@'s residue set @{0, s2, ..., r2*s2}@.
          checkSeg b r =
            b `mod` s2 == 0
            && (r == 0 || s1 `mod` s2 == 0)
            && b + r * s1 <= r2 * s2
      in checkSeg c preR
         && (Prelude.not wraps || checkSeg postBase postR)

-- | /O(w)/. Greatest lower bound: a strided
-- interval that under-approximates the true intersection. Exact when
-- one operand is a singleton or the bases match. Distinct from the
-- lattice 'meet' (which is an over-approximation): 'glb' may /miss/
-- witnesses that lie outside its strided shape but does not invent
-- any. Use 'glb' for path-condition refinement; use 'meet' for lattice
-- work.
--
-- @
-- a:      [*.*.*.*.*.......]   base 0, range 4, stride 2: {0,2,4,6,8}
-- b:      [*..*..*..*..*...]   base 0, range 4, stride 3: {0,3,6,9,12}
-- 'glb':  [*.....*.........]   base 0, range 1, stride 6: {0,6}
-- @
--
-- The cost is /O(log(min(stride si1, stride si2))) = O(log(2^w)) =
-- O(w)/ for the extended-Euclidean Bezout step on the strides; the
-- rest is /O(1)/.
glb ::
  StridedInterval w ->
  StridedInterval w ->
  StridedInterval w
glb si1 si2
  | isBottom si1 || isBottom si2 = bottom (siMask si1)
  | Just v <- asSingleton si1 =
      if member si2 v then si1 else bottom (siMask si1)
  | Just v <- asSingleton si2 =
      if member si1 v then si2 else bottom (siMask si1)
  | base si1 == base si2 = build (base si1)
  -- Lower bound of the intersection: solve
  --   base1 + n * stride1 = base2 + m * stride2
  -- for the least non-negative n in [0, range si1] and m in [0, range si2].
  | Just (n, _) <- solveLinearDiophantine
                     (stride si1) (stride si2)
                     (base si2 - base si1)
                     (siRange si1) (siRange si2) =
      build (base si1 + n * stride si1)
  | otherwise = bottom (siMask si1)
  where
    -- @lo@ is a known common element. Cap the range so that
    -- @(siRange + 1) * s <= 2^w@ - otherwise 'normalize' would widen to
    -- 'top', which is /not/ a sound under-approximation of the
    -- intersection. The cap-imposed range is a sound under-approximation
    -- of the true intersection size.
    build lo =
      let !upper = min (base si1 + span si1)
                       (base si2 + span si2)
          !s = lcm (stride si1) (stride si2)
          !m = siMask si1 + 1
          !rFromUpper = (upper - lo) `div` s
          !rFromCap   = (m `div` s) - 1
          !r          = max 0 (min rFromUpper rFromCap)
      in mkStridedInterval (siMask si1) False lo (lo + r * s) s

-- ---------------------------------------------------------------------------
-- Width manipulation

-- | /O(w)/. Zero-extend a strided interval to a wider type. The set
-- is unchanged; only the declared width changes. Wrapping intervals
-- are handled by splitting into the union of two non-wrapping
-- segments.
--
-- The cost is /O(log(2^w)) = O(w)/ for the gcd inside 'join' on the
-- wrapping branch; /O(1)/ otherwise.
zext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  StridedInterval w ->
  NatRepr u ->
  StridedInterval u
zext si u =
  case fProof of
    LeqProof
      | isBottom si -> bottom (maxUnsigned u)
      | otherwise ->
          let m_old = modulus si
              endRes = (base si + span si) `mod` m_old
          in if endRes >= base si
               -- Non-wrapping: relabel.
               then si { siMask = maxUnsigned u }
               -- Wrapping: cover by the union of the two segments.
               else join (range u (base si) (m_old - 1))
                         (range u 0 endRes)
  where
    wProof :: LeqProof 1 w
    wProof = LeqProof
    uProof :: LeqProof (w + 1) u
    uProof = LeqProof
    fProof :: LeqProof 1 u
    fProof = leqTrans (leqAdd wProof (knownNat :: NatRepr 1)) uProof

-- | /O(w)/. Sign-extend an SI from width @w@ to a wider width @u@.
-- Stride is always preserved: the SI is split at the sign boundary
-- into a non-negative segment (relabeled at the new width) and a
-- negative segment (shifted by the sign-extension amount), and their
-- union is returned.
--
-- The cost is /O(log(2^w)) = O(w)/ for the gcd inside 'join' on the
-- straddling/wrapping branch; /O(1)/ otherwise.
sext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w ->
  StridedInterval w ->
  NatRepr u ->
  StridedInterval u
sext _ si u =
  case fProof of
    LeqProof
      | isBottom si -> bottom (maxUnsigned u)
      | otherwise ->
          let !m_old   = modulus si
              !half    = m_old `div` 2
              !endRes  = (base si + span si) `mod` m_old
              !signExt = (2 ^ natValue u) - m_old
          in if endRes >= base si && endRes < half
             -- Non-wrapping, all non-negative: relabel at the new width.
             then si { siMask = maxUnsigned u }
             else if endRes >= base si && base si >= half
             -- Non-wrapping, all negative: shift the base into the
             -- sign-extended range, preserving stride and range.
             then (si { siMask = maxUnsigned u }) { base = base si + signExt }
             else
               -- Straddles the sign boundary and/or wraps. Split into
               -- non-negative @[0, half-1]@ and negative @[half, m_old-1]@
               -- sub-SIs (each with the same stride), then sign-extend
               -- each separately and join.
               let posPart = clipUnsigned si 0 (half - 1)
                   negPart = case clipUnsigned si half (m_old - 1) of
                               Nothing -> Nothing
                               Just s  -> Just (s { base = base s + signExt })
               in case (posPart, negPart) of
                    (Just p, Just n)  -> join (p { siMask = maxUnsigned u }) (n { siMask = maxUnsigned u })
                    (Just p, Nothing) -> p { siMask = maxUnsigned u }
                    (Nothing, Just n) -> n { siMask = maxUnsigned u }
                    (Nothing, Nothing) -> bottom (maxUnsigned u)
  where
    wProof :: LeqProof 1 w
    wProof = LeqProof
    uProof :: LeqProof (w + 1) u
    uProof = LeqProof
    fProof :: LeqProof 1 u
    fProof = leqTrans (leqAdd wProof (knownNat :: NatRepr 1)) uProof

-- | /O(w)/. Restrict an SI to the elements in the unsigned interval
-- @[lo, hi]@, preserving stride. Returns 'Nothing' if no elements
-- fall in the range. Internal helper for 'sext'; assumes
-- @0 <= lo <= hi < 2^w@.
--
-- Indices @i ∈ [0, range]@ correspond to residues
-- @(base + i*stride) mod m@. The residues march by @stride@ each step
-- and may wrap around @m@ at most once (since @(range + 1) * stride <=
-- m@). The pre-wrap and post-wrap segments are each handled as a
-- contiguous integer range that we intersect with the (shifted) target
-- range to find which @i@s qualify.
--
-- The cost is /O(log(2^w)) = O(w)/ for the gcd inside 'join';
-- otherwise /O(1)/.
clipUnsigned ::
  (1 <= w) =>
  StridedInterval w ->
  Integer ->
  Integer ->
  Maybe (StridedInterval w)
clipUnsigned si lo hi
  | isBottom si = Nothing
  | otherwise =
      let !s    = stride si
          !m    = modulus si
          !rng  = siRange si
          !b    = base si
          -- Index of first wrap-around: first @i@ such that
          -- @b + i*s >= m@. If this is > rng, no wrap.
          !iWrap = ceilDivPos' (m - b) s
          residue i = (b + i * s) `mod` m
          -- Pre-wrap: i in [0, min iWrap - 1, rng]; residues b, b+s, ..., b + i*s without wrap.
          preEnd = min (iWrap - 1) rng
          pre = clipSegment 0 preEnd b
          -- Post-wrap: i in [iWrap, rng]; residues start at @b + iWrap*s - m@.
          post
            | iWrap > rng = Nothing
            | otherwise =
                let !pBase = b + iWrap * s - m
                in clipSegment iWrap rng pBase
          -- Clip a contiguous arithmetic-progression segment
          -- (i in [iLo, iHi], residues startBase + (i - iLo)*s) to
          -- the target range [lo, hi]. The set of qualifying @i@s
          -- forms a contiguous integer range.
          clipSegment iLo iHi startBase
            | iLo > iHi = Nothing
            | endRes < lo = Nothing      -- entirely below
            | startBase > hi = Nothing   -- entirely above
            | otherwise =
                let -- @firstI@: smallest @i@ in @[iLo, iHi]@ with residue >= @lo@
                    firstI = max iLo (iLo + ceilDivPos' (lo - startBase) s)
                    -- @lastI@:  largest  @i@ in @[iLo, iHi]@ with residue <= @hi@
                    lastI  = min iHi (iLo + (hi - startBase) `div` s)
                in if firstI <= lastI
                     then Just StridedInterval
                       { siMask = siMask si
                       , base = residue firstI
                       , siRange = lastI - firstI
                       , stride = s }
                     else Nothing
            where
              endRes = startBase + (iHi - iLo) * s
      in case (pre, post) of
           (Just p, Just q) ->
             -- Both segments contribute. They share stride; whether
             -- they form a single SI or need a join depends on
             -- alignment. Use 'join' for safety.
             Just (join p q)
           (Just p, Nothing) -> Just p
           (Nothing, Just q) -> Just q
           (Nothing, Nothing) -> Nothing
  where
    -- Ceiling division for positive divisor; returns 0 when @x <= 0@.
    ceilDivPos' x y
      | x <= 0 = 0
      | otherwise = (x + y - 1) `div` y

-- | /O(1)/. Concatenate. The result set is @{a * 2^v + b | a ∈ a_dom,
-- b ∈ b_dom}@. When @b@ is a singleton, the high bits inherit @a@'s
-- stride (scaled by @2^v@). When @a@ is a singleton, the high bits
-- are constant and the low bits inherit @b@'s shape (with possible
-- split if @b@ wraps). Otherwise the result mixes both strides — the
-- gcd-of-stride structure may have gaps that don't fit a single
-- strided shape, so we fall back
-- to the contiguous cover.
concat ::
  NatRepr u ->
  StridedInterval u ->
  NatRepr v ->
  StridedInterval v ->
  StridedInterval (u + v)
concat u a v b
  | isBottom a || isBottom b = bottom resultMask
  | Just bv <- asSingleton b =
      -- @{a_i * 2^v + bv}@: stride scales by @2^v@, range preserved.
      normalize StridedInterval { siMask = resultMask
                                , base = base a * shift_v + bv
                                , siRange = siRange a
                                , stride = stride a * shift_v }
  | Just av <- asSingleton a
  , let !endRes_b = (base b + span b) `mod` shift_v
  , endRes_b >= base b =
      -- @{av * 2^v + b_j}@ with non-wrapping @b@: shift @b@'s shape
      -- by @av * 2^v@ in the wider type. (The wrapping case would
      -- require a join, so fall back to Arith below.)
      normalize StridedInterval { siMask = resultMask
                                , base = av * shift_v + base b
                                , siRange = siRange b
                                , stride = stride b }
  | otherwise = fromArith resultMask (A.concat u (toArith a) v (toArith b))
  where
    resultMask = maxUnsigned (addNat u v)
    !shift_v = 2 ^ natValue v

-- | /O(w)/. Select a bit-slice. Mirrors 'What4.Domains.BV.Arith.select'.
select ::
  (1 <= n, i + n <= w) =>
  NatRepr i ->
  NatRepr n ->
  StridedInterval w ->
  StridedInterval n
select i n a
  | isBottom a = bottom (maxUnsigned n)
  | otherwise = fromArith (maxUnsigned n) (A.select i n (toArith a))

-- | /O(1)/. Truncate or relabel a strided interval at width @v@.
trunc ::
  NatRepr v ->
  StridedInterval u ->
  StridedInterval v
trunc w si
  | isBottom si = bottom mask
  | isAny si   = top mask
  -- Already fits at the new width: relabel.
  | span si + stride si <= m =
      normalize si { siMask = mask, base = base si `mod` m }
  -- Stride divides modulus: every residue class is hit.
  | m `mod` stride si == 0 =
      let base_mod_w = base si `mod` m
          base' = (base_mod_w
                  + (stride si * ((m - base_mod_w) `ceilDiv` stride si)))
                  `mod` m
      in normalize StridedInterval { siMask = mask, base = base'
                                   , siRange = (m `ceilDiv` stride si) - 1
                                   , stride = stride si }
  | otherwise = top mask
  where
    mask = maxUnsigned w
    m = mask + 1
    ceilDiv x y = assert (y /= 0) $ (x + y - 1) `div` y

-- ---------------------------------------------------------------------------
-- Arithmetic

-- | /O(w)/. Bitvector addition modulo @2^w@. Mirrors
-- 'What4.Domains.BV.Arith.add' on stride-1 inputs. On strided inputs,
-- preserves the gcd-of-strides structure of the result, which can be
-- strictly tighter than the contiguous Arith cover.
--
-- @
-- a:      [*.*.*...........]   base 0, range 2, stride 2: {0,2,4}
-- b:      [*...*...........]   base 0, range 1, stride 4: {0,4}
-- 'add':  [*.*.*.*.*.......]   base 0, range 4, stride 2: {0,2,4,6,8}
-- @
--
-- Anchors at @base si1 + base si2@ and uses @gcd(stride si1, stride
-- si2)@ as the new stride. Letting @s = gcd(s1, s2)@, the cover has
-- @r1*(s1\/s) + r2*(s2\/s) + 1@ elements spanning @r1*s1 + r2*s2@
-- integers - the same total span as the Arith cover @[lo, lo+r1*s1 +
-- r2*s2]@, but sparser by a factor of @s@. Hence this is always at
-- least as precise as routing through 'A.add' on the contiguous
-- covers, and strictly tighter when @s > 1@.
--
-- When the strided shape exceeds the size cap, 'normalize' drops to a
-- stride-1 cover with the same span - which is exactly the Arith
-- cover. So the SI ≤ A precision relation holds in every case.
--
-- The cost is /O(log(min(stride si1, stride si2))) = O(log(2^w)) =
-- O(w)/ for the gcd of strides; otherwise /O(1)/.
add ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  StridedInterval w
add si1 si2
  | isBottom si1 || isBottom si2 = bottom (siMask si1)
  | Just v <- asSingleton si1 =
      normalize si2 { base = base si2 + v }
  | Just v <- asSingleton si2 =
      normalize si1 { base = base si1 + v }
  | otherwise =
      let !s = gcd (stride si1) (stride si2)
          !r = (siRange si1 * (stride si1 `div` s))
             + (siRange si2 * (stride si2 `div` s))
      in normalize StridedInterval { siMask = siMask si1
                                   , base = base si1 + base si2
                                   , siRange = r
                                   , stride = s
                                   }


-- | /O(w)/. Bitvector add-with-carry. @'Nothing'@ widens the range
-- by one to account for an unknown carry-in.
--
-- The cost is /O(w)/ via 'add' and (in the @'Nothing'@ case) 'join'.
adc ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  Maybe Bool ->
  StridedInterval w
adc si1 si2 _ | isBottom si1 || isBottom si2 = bottom (siMask si1)
adc si1 si2 (Just b) = add si1 (add si2 (singleton (siMask si1) (if b then 1 else 0)))
adc si1 si2 Nothing =
  -- Unknown carry-in: join of (a+b) and (a+b+1).
  join (adc si1 si2 (Just False)) (adc si1 si2 (Just True))

-- | /O(w)/. Bitvector multiplication modulo @2^w@. Bounds the result
-- by taking corner products of the operands' /signed/ representatives
-- (lifting bases that straddle the signed midpoint by @-2^w@), then
-- takes the gcd of the cross-term step strides. On stride-1 inputs
-- this matches 'A.mul' exactly; on strided inputs it can be more
-- precise (the gcd-stride is preserved).
--
-- @
-- a:      [*.*.............]   base 0, range 1, stride 2: {0,2}
-- b:      [...*...*........]   base 3, range 1, stride 4: {3,7}
-- 'mul':  [*.*.*.*.*.*.*.*.]   base 0, range 7, stride 2: {0,2,4,6,8,10,12,14}
-- @
--
-- The product set is @{0,6,14}@ (true product), but a single SI must
-- contain those three points; the gcd-2 cover above is the tightest
-- such SI - any stride > 2 misses one of the three.
--
-- The cost is /O(log(stride si1 * stride si2)) = O(log(2^(2w))) =
-- O(w)/ for the gcd of cross-term step strides; otherwise /O(1)/.
mul ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  StridedInterval w
mul si1 si2
  | isBottom si1 || isBottom si2 = bottom (siMask si1)
  | otherwise =
      let !m    = modulus si1
          !mask = siMask si1
          -- Signed-shift each operand if its unsigned span straddles the
          -- signed midpoint (matches Arith.zbounds).
          lift si =
            if 2 * base si + span si > mask
              then base si - m else base si
          !lo1 = lift si1
          !lo2 = lift si2
          !hi1 = lo1 + span si1
          !hi2 = lo2 + span si2
          -- The product (b1 + i*s1)(b2 + j*s2) is bilinear in (i, j) over the
          -- rectangle [0, r1] x [0, r2], so its extrema lie at the corners.
          !ll = lo1 * lo2
          !lh = lo1 * hi2
          !hl = hi1 * lo2
          !hh = hi1 * hi2
          !cl = ll `min` lh `min` hl `min` hh
          !ch = ll `max` lh `max` hl `max` hh
          -- Stride: gcd of the three cross-term step strides
          -- (s1*lo2, s2*lo1, s1*s2), suppressing terms where the
          -- corresponding index is fixed (range = 0). 'abs' first because
          -- lifted bases can be negative; @gcd 0 x = x@ handles the
          -- suppressed terms.
          !step1  = if siRange si1 == 0 then 0 else abs (stride si1 * lo2)
          !step2  = if siRange si2 == 0 then 0 else abs (stride si2 * lo1)
          !step12 = if siRange si1 == 0 || siRange si2 == 0 then 0
                    else stride si1 * stride si2
          !sRaw   = gcd (gcd step1 step2) step12
          !s      = if sRaw == 0 then 1 else sRaw
      in normalize StridedInterval { siMask = mask
                                   , base = cl `mod` m
                                   , siRange = (ch - cl) `div` s
                                   , stride = s
                                   }

-- | /O(1)/. Negation modulo @2^w@. Mirrors 'What4.Domains.BV.Arith.negate'.
negate ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w
negate si
  | isBottom si = si
  | otherwise =
      normalize si { base = Prelude.negate (base si + span si) }

-- | /O(w)/. Subtraction modulo @2^w@. Mirrors
-- 'What4.Domains.BV.Arith.add' composed with 'A.negate' on stride-1
-- inputs; on strided inputs, preserves the gcd-of-strides structure.
--
-- @
-- a:                [**..............]   base 0,  range 1, stride 1: {0,1}
-- b:                [*.......*.......]   base 0,  range 1, stride 8: {0,8}
-- 'sub' (native):   [********......**]   base 8,  range 9, stride 1: wraps to {0,1}
-- @
--
-- Compare to @'add' a ('negate' b)@:
--
-- @
-- 'negate' b:       [*.......*.......]   base 0,  range 1, stride 8: {0,8}  (set unchanged; dewrap rotated the AP)
-- a + 'negate' b:   [**********......]   base 0,  range 9, stride 1: {0..9} (non-wrapping, looser)
-- @
--
-- Anchors at @base si1 - base si2 - span si2@ (the
-- smallest corner of the difference rectangle - the most negative
-- @a_i - b_j@) and uses @gcd(stride si1, stride si2)@ as the new
-- stride. Going native rather than @add a (negate b)@ matters because
-- 'negate' canonicalizes via 'normalize''s @dewrap@ step, which
-- dewraps @(range+1)*stride == 2^w@ shapes to a non-wrapping anchor;
-- that loses the rotation that 'A.negate' picks for the contiguous
-- cover.
--
-- The cost is /O(log(min(stride si1, stride si2))) = O(log(2^w)) =
-- O(w)/ for the gcd of strides; otherwise /O(1)/.
sub ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  StridedInterval w
sub si1 si2
  | isBottom si1 || isBottom si2 = bottom (siMask si1)
  | Just v <- asSingleton si2 =
      normalize si1 { base = base si1 - v }
  | otherwise =
      let !s = gcd (stride si1) (stride si2)
          !r = (siRange si1 * (stride si1 `div` s))
             + (siRange si2 * (stride si2 `div` s))
      in normalize StridedInterval
           { siMask = siMask si1
           , base = base si1 - base si2 - span si2
           , siRange = r
           , stride = s
           }

-- | /O(1)/. Multiply every element of @si@ by a scalar @k@, modulo
-- @2^w@. Mirrors 'What4.Domains.BV.Arith.scale'. The scalar is
-- interpreted as a /signed/ integer at width @w@ (matching Arith).
scale ::
  (1 <= w) =>
  Integer ->
  StridedInterval w ->
  StridedInterval w
scale _ si | isBottom si = si
scale k si
  | k' == 0 = singleton (siMask si) 0
  | k' >= 0 =
      normalize si { base = base si * k', stride = stride si * k' }
  | otherwise =
      -- Negate first (preserves stride), then scale by |k|.
      let neg = negate si
      in normalize neg { base = base neg * abs k', stride = stride neg * abs k' }
  where
    k' = maskSigned (siMask si) k

-- | /O(1)/. Bitwise complement modulo @2^w@. Mirrors 'What4.Domains.BV.Arith.not'.
not ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w
not si
  | isBottom si = si
  | otherwise =
      normalize si { base = siMask si
                          - (base si + span si) }

-- | /O(w)/. Bitwise AND. Converts both operands to the
-- 'What4.Domains.BV.Bitwise' domain, applies 'B.and', and converts
-- back to a stride-1 interval.
and ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  StridedInterval w
and a b
  | isBottom a || isBottom b = bottom (siMask a)
  | otherwise = fromBitwise (siMask a) (B.and (toBitwise a) (toBitwise b))
{-# INLINE and #-}

-- | /O(w)/. Bitwise OR. Converts both operands to the
-- 'What4.Domains.BV.Bitwise' domain, applies 'B.or', and converts
-- back to a stride-1 interval.
or ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  StridedInterval w
or a b
  | isBottom a || isBottom b = if isBottom a then b else a
  | otherwise = fromBitwise (siMask a) (B.or (toBitwise a) (toBitwise b))
{-# INLINE or #-}

-- | /O(w)/. Bitwise XOR. Converts both operands to the
-- 'What4.Domains.BV.Bitwise' domain, applies 'B.xor', and converts
-- back to a stride-1 interval.
xor ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  StridedInterval w
xor a b
  | isBottom a || isBottom b = if isBottom a then b else a
  | otherwise = fromBitwise (siMask a) (B.xor (toBitwise a) (toBitwise b))
{-# INLINE xor #-}

-- | Convert an SI to a Bitwise domain via its bitwise bounds.
toBitwise :: (1 <= w) => StridedInterval w -> B.Domain w
toBitwise si = B.interval (siMask si) lo hi
  where (lo, hi) = bitbounds si
{-# INLINE toBitwise #-}

-- | Convert a Bitwise domain back to a stride-1 SI.
fromBitwise :: Integer -> B.Domain w -> StridedInterval w
fromBitwise mask bw = assert (validMask mask) $
  let (lo, hi) = B.ubounds bw
  in if hi - lo >= mask then top mask
     else StridedInterval { siMask = mask, base = lo, siRange = hi - lo, stride = 1 }
{-# INLINE fromBitwise #-}

-- | /O(w)/. Left shift. When the shift amount is a singleton @k@,
-- scales by @2^k@ (preserving stride structure) or returns 0 if
-- @k >= w@. Otherwise routes through 'A.shl' on the contiguous cover.
--
-- The cost is /O(w)/ for the @A.shl@ cover fallback; /O(1)/ on the
-- singleton-shift path.
shl ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  StridedInterval w ->
  StridedInterval w
shl w a b
  | isBottom a || isBottom b = bottom (siMask a)
  | Just k <- asSingleton b =
      if k >= intValue w
        then singleton (siMask a) 0
        else scale (2 ^ k) a
  | otherwise =
      -- Non-singleton shift amount: route through 'A.shl' on the cover,
      -- which uses Arith's @mulRange@-of-@zbounds@ trick to produce a
      -- tighter cover than enumerating shifts and joining would.
      fromArith (siMask a) (A.shl w (toArith a) (toArith b))

-- | /O(w)/. Logical right shift. When the shift amount is a singleton
-- @k@, divides every element by @2^k@ (preserving the strided shape
-- when the operand's stride is divisible by @2^k@); otherwise routes
-- through 'A.lshr' on the unsigned cover.
lshr ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  StridedInterval w ->
  StridedInterval w
lshr w a b
  | isBottom a || isBottom b = bottom (siMask a)
  | Just k <- asSingleton b =
      if k >= intValue w
        then singleton (siMask a) 0
        else lshrConst w a k
  | otherwise = fromArith (siMask a) (A.lshr w (toArith a) (toArith b))

-- | /O(1)/. Internal: @lshrConst a k@ shifts every element of @a@
-- right by @k >= 0@ bits, preserving stride when possible.
--
-- If @a@ is non-wrapping and its stride is divisible by @2^k@, the
-- result is @a@ with each element divided by @2^k@: same range, new
-- stride @stride a / 2^k@, new base @base a `shiftR` k@. Otherwise we
-- route through the contiguous Arith cover.
lshrConst ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  Integer ->
  StridedInterval w
lshrConst w a k
  | k == 0 = a
  | otherwise =
      let !m = modulus a
          !endRes = (base a + span a) `mod` m
          !wraps = endRes < base a
          !shift_k = 2 ^ k
          arithFallback =
            fromArith (siMask a) (A.lshr w (toArith a)
                                (toArith (singleton (siMask a) k)))
      in if wraps then arithFallback
         else if stride a `mod` shift_k == 0
         then normalize StridedInterval { siMask = siMask a
                                        , base = base a `Bits.shiftR` fromInteger k
                                        , siRange = siRange a
                                        , stride = stride a `div` shift_k }
         else arithFallback

-- | /O(w)/. Arithmetic right shift. Routes through 'A.ashr' on the
-- unsigned cover.
ashr ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  StridedInterval w ->
  StridedInterval w
ashr w a b
  | isBottom a || isBottom b = bottom (siMask a)
  | otherwise = fromArith (siMask a) (A.ashr w (toArith a) (toArith b))

-- | /O(w²)/. Rotate left. Converts to the 'What4.Domains.BV.Bitwise'
-- domain, applies 'B.rolAbstract', and converts back to a stride-1 SI.
rol ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  StridedInterval w ->
  StridedInterval w
rol w a b
  | isBottom a || isBottom b = bottom (siMask a)
  | otherwise = fromBitwise (siMask a) (B.rolAbstract w (toBitwise a) (toBitwise b))
{-# INLINE rol #-}

-- | /O(w²)/. Rotate right. Converts to the 'What4.Domains.BV.Bitwise'
-- domain, applies 'B.rorAbstract', and converts back to a stride-1 SI.
ror ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  StridedInterval w ->
  StridedInterval w
ror w a b
  | isBottom a || isBottom b = bottom (siMask a)
  | otherwise = fromBitwise (siMask a) (B.rorAbstract w (toBitwise a) (toBitwise b))
{-# INLINE ror #-}

-- | /O(w)/. Unsigned division. Routes through 'A.udiv' on the unsigned cover.
udiv ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  StridedInterval w
udiv a b
  | isBottom a || isBottom b = bottom (siMask a)
  | otherwise = fromArith (siMask a) (A.udiv (toArith a) (toArith b))

-- | /O(w)/. Unsigned remainder. Routes through 'A.urem' on the unsigned cover.
urem ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  StridedInterval w
urem a b
  | isBottom a || isBottom b = bottom (siMask a)
  | otherwise = fromArith (siMask a) (A.urem (toArith a) (toArith b))

-- | /O(w)/. Signed division. Routes through 'A.sdiv' on the unsigned cover.
sdiv ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  StridedInterval w ->
  StridedInterval w
sdiv w a b
  | isBottom a || isBottom b = bottom (maxUnsigned w)
  | otherwise = fromArith (maxUnsigned w) (A.sdiv w (toArith a) (toArith b))

-- | /O(w)/. Signed remainder. Routes through 'A.srem' on the unsigned cover.
srem ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  StridedInterval w ->
  StridedInterval w
srem w a b
  | isBottom a || isBottom b = bottom (maxUnsigned w)
  | otherwise = fromArith (maxUnsigned w) (A.srem w (toArith a) (toArith b))

-- ---------------------------------------------------------------------------
-- Destructors

-- | /O(siRange) = O(2^w)/. Enumerate all elements of the SI.
toList :: StridedInterval w -> [Integer]
toList si
  | isBottom si = []
  | otherwise  =
      let m = modulus si
      in [ (base si + stride si * i) `mod` m | i <- [0 .. siRange si] ]

-- | /O(1)/. Inclusive @(lo, hi)@ unsigned bounds. For wrapping or
-- 'any' SIs, returns @(0, maxUnsigned w)@. Empty is treated like
-- 'any' (callers should check 'isEmpty' first if they care).
ubounds :: StridedInterval w -> (Integer, Integer)
ubounds si
  | isBottom si = (0, siMask si)
  | isAny si   = (0, siMask si)
  | otherwise  =
      let !m = modulus si
          !endRes = (base si + span si) `mod` m
      in if endRes >= base si
           then (base si, endRes)
           else (0, siMask si)

-- | /O(w)/. Inclusive @(lo, hi)@ signed bounds. Mirrors
-- 'What4.Domains.BV.Arith.sbounds'.
sbounds :: (1 <= w) => NatRepr w -> StridedInterval w -> (Integer, Integer)
sbounds w si
  | isBottom si = (Prelude.negate halfRange, halfRange - 1)
  | otherwise = A.sbounds w (toArith si)
  where
    halfRange = 2 ^ (natValue w - 1)

-- | /O(1)/. Bitwise bounds for the domain: @(bitwise-AND of all
-- elements, bitwise-OR of all elements)@. Refined using 'unknowns'
-- (which masks out the low bits fixed by the stride).
bitbounds :: (1 <= w) => StridedInterval w -> (Integer, Integer)
bitbounds si
  | isBottom si = (0, 0)
  | otherwise =
      let !u  = unknowns si
          !b  = base si
          !hi = b Bits..|. u
          !lo = hi `Bits.xor` u
      in (lo, hi)

-- | /O(1)/. Bitmask of bit positions whose values are not constant
-- across the elements of the domain.
unknowns :: (1 <= w) => StridedInterval w -> Integer
unknowns si
  | isBottom si = 0
  | otherwise =
      let !aUnknowns = A.unknowns (toArith si)
          -- The largest power of two dividing @stride@. The low bits
          -- below it equal the corresponding bits of @base@ across
          -- every element of the SI, hence they don't vary.
          !lowFixed = (stride si Bits..&. Prelude.negate (stride si)) - 1
      in aUnknowns Bits..&. Bits.complement lowFixed

-- | /O(w)/. Equality test. Mirrors 'What4.Domains.BV.Arith.eq'. Returns
-- @Just True@ when both operands are the same singleton, @Just False@
-- when the domains are provably disjoint, @Nothing@ otherwise.
eq :: StridedInterval w -> StridedInterval w -> Maybe Bool
eq a b
  | Just x <- asSingleton a, Just y <- asSingleton b = Just (x == y)
  | Prelude.not (domainsOverlap a b) = Just False
  | otherwise = Nothing

-- | /O(1)/. Unsigned less-than test. Mirrors 'What4.Domains.BV.Arith.ult'.
ult :: (1 <= w) => StridedInterval w -> StridedInterval w -> Maybe Bool
ult a b
  | a_max < b_min = Just True
  | a_min >= b_max = Just False
  | otherwise = Nothing
  where
    (a_min, a_max) = ubounds a
    (b_min, b_max) = ubounds b

-- | /O(w)/. Signed less-than test. Mirrors 'What4.Domains.BV.Arith.slt'.
slt :: (1 <= w) => NatRepr w -> StridedInterval w -> StridedInterval w -> Maybe Bool
slt w a b
  | a_max < b_min = Just True
  | a_min >= b_max = Just False
  | otherwise = Nothing
  where
    (a_min, a_max) = sbounds w a
    (b_min, b_max) = sbounds w b

-- ---------------------------------------------------------------------------
-- Correctness properties

-- ---------------------------------------------------------------------------
-- Generators

-- | Random generator for proper strided-interval domain values.
-- Produces a mix of empty, singleton, non-wrapping strided, and wrapping
-- strided intervals.
genDomain :: NatRepr w -> Gen (StridedInterval w)
genDomain w =
  do let mask = maxUnsigned w
         m = mask + 1
     sz <- getSize
     shape <- chooseInt (0, 11 :: Int)
     case shape of
       0 -> pure (bottom mask)
       1 -> singleton mask <$> chooseInteger (0, mask)
       _ ->
         -- Pick r >= 1 first, then pick s so that (r + 1) * s <= m. This
         -- automatically excludes the uncanonical "stride > 1, range 0"
         -- shape (which is just a singleton with the wrong stride).
         do b <- chooseInteger (0, mask)
            let rCap = max 1 (min (toInteger sz) (mask))
            r <- chooseInteger (1, rCap)
            let strideCap = max 1 (min (toInteger sz) (m `div` (r + 1)))
            s <- chooseInteger (1, strideCap)
            -- Avoid the uncanonical "full set" shape (covered by 'top').
            let !full = r == mask && s == 1 && b /= 0
            pure StridedInterval { siMask = mask
                                 , base = if full then 0 else b
                                 , siRange = r
                                 , stride = s
                                 }

-- | Generate an element of a non-empty strided interval. If the input is
-- empty, generates 0; properties using the result must guard with
-- @member a x ==> ...@.
genElement :: StridedInterval w -> Gen Integer
genElement si
  | isBottom si = pure 0
  | otherwise =
      do i <- chooseInteger (0, siRange si)
         pure ((base si + stride si * i) `mod` modulus si)

-- | Generate a domain paired with one of its elements.
genPair :: NatRepr w -> Gen (StridedInterval w, Integer)
genPair w =
  do a <- genDomain w
     x <- genElement a
     pure (a, x)

-- ---------------------------------------------------------------------------
-- Invariant postconditions

correct_proper_bottom :: NatRepr w -> Property
correct_proper_bottom w = property (proper (bottom (maxUnsigned w)))

correct_proper_top :: NatRepr w -> Property
correct_proper_top w = property (proper (top (maxUnsigned w)))

correct_proper_singleton :: NatRepr w -> Integer -> Property
correct_proper_singleton w v = property (proper (singleton (maxUnsigned w) v))

correct_proper_mkStridedInterval ::
  NatRepr w ->
  Bool ->
  Integer ->
  Integer ->
  Integer ->
  Property
correct_proper_mkStridedInterval w roundUp lo hi s =
  property (proper (mkStridedInterval (maxUnsigned w) roundUp lo hi s))

correct_proper_range ::
  NatRepr w ->
  Integer ->
  Integer ->
  Property
correct_proper_range w lo hi = property (proper (range w lo hi))

correct_proper_fromAscEltList :: NatRepr w -> [Integer] -> Property
correct_proper_fromAscEltList w vs = property (proper (fromAscEltList w vs))

correct_proper_join ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  Property
correct_proper_join a b = property (proper (join a b))

correct_proper_unionSingleton ::
  (1 <= w) =>
  StridedInterval w ->
  Integer ->
  Property
correct_proper_unionSingleton si v = property (proper (unionSingleton v si))

correct_proper_glb ::
  StridedInterval w ->
  StridedInterval w ->
  Property
correct_proper_glb a b = property (proper (glb a b))

correct_proper_add ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  Property
correct_proper_add a b = property (proper (add a b))

correct_proper_adc ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  Maybe Bool ->
  Property
correct_proper_adc a b c = property (proper (adc a b c))

correct_proper_mul ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  Property
correct_proper_mul a b = property (proper (mul a b))

correct_proper_sub ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  Property
correct_proper_sub a b = property (proper (sub a b))

correct_proper_negate ::
  (1 <= w) =>
  StridedInterval w ->
  Property
correct_proper_negate si = property (proper (negate si))

correct_proper_scale ::
  (1 <= w) =>
  Integer ->
  StridedInterval w ->
  Property
correct_proper_scale k si = property (proper (scale k si))

correct_proper_not ::
  (1 <= w) =>
  StridedInterval w ->
  Property
correct_proper_not si = property (proper (not si))

correct_proper_and ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  Property
correct_proper_and a b = property (proper (and a b))

correct_proper_or ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  Property
correct_proper_or a b = property (proper (or a b))

correct_proper_xor ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  Property
correct_proper_xor a b = property (proper (xor a b))

correct_proper_shl ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  StridedInterval w ->
  Property
correct_proper_shl w a b = property (proper (shl w a b))

correct_proper_lshr ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  StridedInterval w ->
  Property
correct_proper_lshr w a b = property (proper (lshr w a b))

correct_proper_ashr ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  StridedInterval w ->
  Property
correct_proper_ashr w a b = property (proper (ashr w a b))

correct_proper_rol ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  StridedInterval w ->
  Property
correct_proper_rol w a b = property (proper (rol w a b))

correct_proper_ror ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  StridedInterval w ->
  Property
correct_proper_ror w a b = property (proper (ror w a b))

correct_proper_udiv ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  Property
correct_proper_udiv a b = property (proper (udiv a b))

correct_proper_urem ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  Property
correct_proper_urem a b = property (proper (urem a b))

correct_proper_sdiv ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  StridedInterval w ->
  Property
correct_proper_sdiv w a b = property (proper (sdiv w a b))

correct_proper_srem ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  StridedInterval w ->
  Property
correct_proper_srem w a b = property (proper (srem w a b))

correct_proper_concat ::
  NatRepr u ->
  StridedInterval u ->
  NatRepr v ->
  StridedInterval v ->
  Property
correct_proper_concat u a v b = property (proper (concat u a v b))

correct_proper_select ::
  (1 <= n, i + n <= w) =>
  NatRepr i ->
  NatRepr n ->
  StridedInterval w ->
  Property
correct_proper_select i n a = property (proper (select i n a))

correct_proper_trunc :: NatRepr v -> StridedInterval w -> Property
correct_proper_trunc v si = property (proper (trunc v si))

correct_proper_zext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  StridedInterval w ->
  NatRepr u ->
  Property
correct_proper_zext si u = property (proper (zext si u))

correct_proper_sext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w ->
  StridedInterval w ->
  NatRepr u ->
  Property
correct_proper_sext w si u = property (proper (sext w si u))

-- ---------------------------------------------------------------------------
-- Predicates

correct_toList_member :: StridedInterval w -> Property
correct_toList_member si =
  property (Prelude.all (member si) (toList si))

correct_member_toList ::
  StridedInterval w ->
  Integer ->
  Property
correct_member_toList si x =
  member si x ==> elem (x `mod` modulus si) (toList si)

correct_asSingleton :: StridedInterval w -> Property
correct_asSingleton si =
  case asSingleton si of
    Just v  -> property (toList si == [v])
    Nothing -> property True

correct_domainsOverlap ::
  StridedInterval w ->
  StridedInterval w ->
  Integer ->
  Property
correct_domainsOverlap a b x =
  member a x ==> member b x ==> domainsOverlap a b

correct_domainsOverlap_bottom :: StridedInterval w -> Property
correct_domainsOverlap_bottom si =
  property (Prelude.not (domainsOverlap (bottom (siMask si)) si))

-- ---------------------------------------------------------------------------
-- Lattice operations

-- | 'join' is sound: if @x@ is in either @a@ or @b@, then @x@ is in
-- @join a b@.
correct_join ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  Integer ->
  Property
correct_join a b x =
  (member a x || member b x) ==> member (join a b) x

-- | 'meet' is a sound /over/-approximation of intersection: if @x@ is in
-- both @a@ and @b@, then @x@ is in @meet a b@.
correct_meet ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  Integer ->
  Property
correct_meet a b x =
  (member a x && member b x) ==> member (meet a b) x

-- | 'leq' is a sound under-approximation of the subset relation: if
-- @leq a b@ holds and @x@ is in @a@, then @x@ is in @b@.
correct_leq ::
  StridedInterval w ->
  StridedInterval w ->
  Integer ->
  Property
correct_leq a b x =
  (leq a b && member a x) ==> member b x

correct_unionSingleton ::
  (1 <= w) =>
  StridedInterval w ->
  Integer ->
  Property
correct_unionSingleton si v =
  property (member (unionSingleton v si) v)

correct_glb ::
  StridedInterval w ->
  StridedInterval w ->
  Integer ->
  Property
correct_glb a b x =
  member (glb a b) x ==> member a x && member b x

correct_glb_singleton_left ::
  NatRepr w ->
  Integer ->
  StridedInterval w ->
  Property
correct_glb_singleton_left w v si =
  let s = singleton (maxUnsigned w) v
  in member si v ==> member (glb s si) v

correct_glb_singleton_right ::
  NatRepr w ->
  Integer ->
  StridedInterval w ->
  Property
correct_glb_singleton_right w v si =
  let s = singleton (maxUnsigned w) v
  in member si v ==> member (glb si s) v

-- ---------------------------------------------------------------------------
-- Lattice laws (semantic, i.e. same set of members)

join_commutative ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  Integer ->
  Property
join_commutative a b x =
  property (member (join a b) x == member (join b a) x)

join_idempotent ::
  (1 <= w) =>
  StridedInterval w ->
  Integer ->
  Property
join_idempotent a x =
  property (member (join a a) x == member a x)

meet_commutative ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  Integer ->
  Property
meet_commutative a b x =
  property (member (meet a b) x == member (meet b a) x)

meet_idempotent ::
  (1 <= w) =>
  StridedInterval w ->
  Integer ->
  Property
meet_idempotent a x =
  property (member (meet a a) x == member a x)

join_top ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  Integer ->
  Property
join_top w a x =
  property (member (join a (top (maxUnsigned w))) x)

join_bottom ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  Integer ->
  Property
join_bottom w a x =
  property (member (join a (bottom (maxUnsigned w))) x == member a x)

meet_top ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  Integer ->
  Property
meet_top w a x =
  property (member (meet a (top (maxUnsigned w))) x == member a x)

meet_bottom ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  Integer ->
  Property
meet_bottom w a x =
  property (Prelude.not (member (meet a (bottom (maxUnsigned w))) x))

leq_reflexive :: StridedInterval w -> Property
leq_reflexive a = property (leq a a)

join_upper_bound ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  Property
join_upper_bound a b = property (leq a (join a b))

join_proper ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  Property
join_proper a b = property (proper (join a b))

meet_proper ::
  (1 <= w) =>
  StridedInterval w ->
  StridedInterval w ->
  Property
meet_proper a b = property (proper c)
  where c = meet a b

-- ---------------------------------------------------------------------------
-- Width manipulation

correct_concat ::
  NatRepr u ->
  (StridedInterval u, Integer) ->
  NatRepr v ->
  (StridedInterval v, Integer) ->
  Property
correct_concat u (a, x) v (b, y) =
  member a x ==> member b y ==>
    member (concat u a v b)
           (toUnsigned u x * 2 ^ natValue v + toUnsigned v y)

correct_select ::
  (1 <= n, i + n <= w) =>
  NatRepr i ->
  NatRepr n ->
  (StridedInterval w, Integer) ->
  Property
correct_select i n (a, x) =
  member a x ==>
    let !shifted = (x `mod` modulus a) `div` (2 ^ natValue i)
    in member (select i n a) (toUnsigned n shifted)

correct_trunc ::
  NatRepr v ->
  (StridedInterval w, Integer) ->
  Property
correct_trunc v (si, x) =
  member si x ==> member (trunc v si) (toUnsigned v x)

correct_zext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  StridedInterval w ->
  NatRepr u ->
  Integer ->
  Property
correct_zext si u x =
  member si x ==>
    member (zext si u) (x `mod` modulus si)

correct_sext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w ->
  StridedInterval w ->
  NatRepr u ->
  Integer ->
  Property
correct_sext w si u x =
  member si x ==>
    member (sext w si u) (toSigned w x)

-- ---------------------------------------------------------------------------
-- Arithmetic

correct_add ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  (StridedInterval w, Integer) ->
  Property
correct_add w (a, x) (b, y) =
  member a x ==> member b y ==>
    member (add a b) ((x + y) `mod` modulusN w)

correct_adc ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  (StridedInterval w, Integer) ->
  Bool ->
  Property
correct_adc w (a, x) (b, y) c =
  member a x ==> member b y ==>
    member (adc a b (Just c))
           ((x + y + (if c then 1 else 0)) `mod` modulusN w)

correct_sub ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  (StridedInterval w, Integer) ->
  Property
correct_sub w (a, x) (b, y) =
  member a x ==> member b y ==>
    member (sub a b) ((x - y) `mod` modulusN w)

correct_negate ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  Property
correct_negate w (a, x) =
  member a x ==>
    member (negate a) ((Prelude.negate x) `mod` modulusN w)

correct_scale ::
  (1 <= w) =>
  NatRepr w ->
  Integer ->
  (StridedInterval w, Integer) ->
  Property
correct_scale w k (a, x) =
  member a x ==>
    member (scale k a) ((toSigned w k * x) `mod` modulusN w)

correct_mul ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  (StridedInterval w, Integer) ->
  Property
correct_mul w (a, x) (b, y) =
  member a x ==> member b y ==>
    member (mul a b) ((x * y) `mod` modulusN w)

correct_udiv ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  (StridedInterval w, Integer) ->
  Property
correct_udiv _ (a, x) (b, y) =
  member a x ==> member b y ==> y' /= 0 ==>
    member (udiv a b) (x' `quot` y')
  where
    x' = maskUnsigned (siMask a) x
    y' = maskUnsigned (siMask b) y

correct_urem ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  (StridedInterval w, Integer) ->
  Property
correct_urem _ (a, x) (b, y) =
  member a x ==> member b y ==> y' /= 0 ==>
    member (urem a b) (x' `rem` y')
  where
    x' = maskUnsigned (siMask a) x
    y' = maskUnsigned (siMask b) y

correct_sdiv ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  (StridedInterval w, Integer) ->
  Property
correct_sdiv w (a, x) (b, y) =
  member a x ==> member b y ==> y' /= 0 ==>
    member (sdiv w a b) (x' `quot` y')
  where
    x' = toSigned w x
    y' = toSigned w y

correct_srem ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  (StridedInterval w, Integer) ->
  Property
correct_srem w (a, x) (b, y) =
  member a x ==> member b y ==> y' /= 0 ==>
    member (srem w a b) (x' `rem` y')
  where
    x' = toSigned w x
    y' = toSigned w y

correct_not ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  Property
correct_not w (a, x) =
  member a x ==>
    member (not a) (Bits.complement x Bits..&. maxUnsigned w)

correct_and ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  (StridedInterval w, Integer) ->
  Property
correct_and _w (a, x) (b, y) =
  member a x ==> member b y ==>
    member (and a b) (x Bits..&. y)

correct_or ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  (StridedInterval w, Integer) ->
  Property
correct_or _w (a, x) (b, y) =
  member a x ==> member b y ==>
    member (or a b) (x Bits..|. y)

correct_xor ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  (StridedInterval w, Integer) ->
  Property
correct_xor _w (a, x) (b, y) =
  member a x ==> member b y ==>
    member (xor a b) (x `Bits.xor` y)

correct_shl ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  (StridedInterval w, Integer) ->
  Property
correct_shl w (a, x) (b, k) =
  member a x ==> member b k ==>
    let expected
          | k >= toInteger (natValue w) = 0
          | otherwise = (x * (2 ^ k)) `mod` modulusN w
    in member (shl w a b) expected

correct_lshr ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  (StridedInterval w, Integer) ->
  Property
correct_lshr w (a, x) (b, k) =
  member a x ==> member b k ==>
    let z = toUnsigned w x `Bits.shiftR` fromInteger (min (intValue w) k)
    in member (lshr w a b) z

correct_ashr ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  (StridedInterval w, Integer) ->
  Property
correct_ashr w (a, x) (b, k) =
  member a x ==> member b k ==>
    let z = toSigned w x `Bits.shiftR` fromInteger (min (intValue w) k)
    in member (ashr w a b) z

correct_rol ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  (StridedInterval w, Integer) ->
  Property
correct_rol w (a, x) (b, k) =
  member a x ==> member b k ==>
    member (rol w a b) (Arith.rotateLeft w x k)

correct_ror ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  (StridedInterval w, Integer) ->
  Property
correct_ror w (a, x) (b, k) =
  member a x ==> member b k ==>
    member (ror w a b) (Arith.rotateRight w x k)

-- ---------------------------------------------------------------------------
-- Destructors

correct_size :: (StridedInterval w, Integer) -> Property
correct_size (si, _) =
  property (size si == toInteger (length (toList si)))

correct_ubounds ::
  StridedInterval w ->
  Integer ->
  Property
correct_ubounds si x =
  member si x ==>
    let (lo, hi) = ubounds si
        x'      = x `mod` modulus si
    in lo <= x' && x' <= hi

correct_ubounds_bottom :: NatRepr w -> Property
correct_ubounds_bottom w = property (isBottom (bottom (maxUnsigned w)))

correct_sbounds ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  Property
correct_sbounds w (a, x) =
  member a x ==>
    let (lo, hi) = sbounds w a
        x'      = toSigned w x
    in lo <= x' && x' <= hi

correct_bitbounds ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  Property
correct_bitbounds _ (a, x) =
  member a x ==>
    let (lo, hi) = bitbounds a
        x'      = x `mod` modulus a
    in (x' Bits..|. lo) == x' && (x' Bits..|. hi) == hi

correct_unknowns ::
  (1 <= w) =>
  NatRepr w ->
  StridedInterval w ->
  Integer ->
  Integer ->
  Property
correct_unknowns _ a x y =
  member a x ==> member a y ==>
    let u = unknowns a
    in (x Bits..|. u) == (y Bits..|. u)

correct_eq ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  (StridedInterval w, Integer) ->
  Property
correct_eq w (a, x) (b, y) =
  member a x ==> member b y ==>
    case eq a b of
      Just True  -> toUnsigned w x == toUnsigned w y
      Just False -> toUnsigned w x /= toUnsigned w y
      Nothing    -> True

correct_ult ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  (StridedInterval w, Integer) ->
  Property
correct_ult w (a, x) (b, y) =
  member a x ==> member b y ==>
    case ult a b of
      Just True  -> toUnsigned w x < toUnsigned w y
      Just False -> toUnsigned w x >= toUnsigned w y
      Nothing    -> True

correct_slt ::
  (1 <= w) =>
  NatRepr w ->
  (StridedInterval w, Integer) ->
  (StridedInterval w, Integer) ->
  Property
correct_slt w (a, x) (b, y) =
  member a x ==> member b y ==>
    case slt w a b of
      Just True  -> toSigned w x < toSigned w y
      Just False -> toSigned w x >= toSigned w y
      Nothing    -> True

-- ---------------------------------------------------------------------------
-- Bottom edge cases

correct_glb_bottom_left :: StridedInterval w -> Property
correct_glb_bottom_left a = property (isBottom (glb (bottom (siMask a)) a))

correct_glb_bottom_right :: StridedInterval w -> Property
correct_glb_bottom_right a = property (isBottom (glb a (bottom (siMask a))))

correct_add_bottom_left ::
  (1 <= w) =>
  NatRepr w -> StridedInterval w -> Property
correct_add_bottom_left w a = property (isBottom (add (bottom (maxUnsigned w)) a))

correct_add_bottom_right ::
  (1 <= w) =>
  NatRepr w -> StridedInterval w -> Property
correct_add_bottom_right w a = property (isBottom (add a (bottom (maxUnsigned w))))

correct_mul_bottom_left ::
  (1 <= w) =>
  NatRepr w -> StridedInterval w -> Property
correct_mul_bottom_left w a = property (isBottom (mul (bottom (maxUnsigned w)) a))

correct_mul_bottom_right ::
  (1 <= w) =>
  NatRepr w -> StridedInterval w -> Property
correct_mul_bottom_right w a = property (isBottom (mul a (bottom (maxUnsigned w))))

-- Helper.
modulusN :: NatRepr w -> Integer
modulusN w = 2 ^ natValue w

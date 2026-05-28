{-|
Module      : What4.Domains.BV.CLP
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Circular linear progressions (CLPs) are an interval-like abstract domain for
bitvectors. A CLP is a tuple @(start, stride, n)@ representing the sequence
of @n + 1@ distinct bitvectors visited by walking @n@ steps of size @stride@
from @start@ (mod @2^w@):

@
{ start + i * stride mod 2^w | 0 <= i <= n }
@

Notably, this representation allows for intervals that wrap around 0, and
even for intervals that wrap around their starting points, even multiple
times (while still visiting only distinct bitvectors). The interval domain in
"What4.Domains.BV.Arith" can be thought of as a CLP with @stride = 1@.

It is common to conceptualize these progressions as intervals that proceed
clockwise around a \"number circle\", starting at 0 at the south pole,
proceeding around to the signed maximum at the north pole (and then immediately
to the signed minimum), and ending at the unsigned maximum just before 0.

@
smax = 011..1 --vv-- 100..0 = smin
                --
              /    \
              \    /
                --
umin = 000..0 --^^-- 111..1 = umax
@

This module does not define lattice operations and enforces that all of its
inputs and outputs are non-bottom ('proper') CLPs. For a pseudo-lattice
structure on top of CLPs, see "What4.Domains.BV.StridedInteravl"

Related domains in the literature:

* The canonical reference for CLPs is /Executable Analysis using Abstract
  Interpretation with Circular Linear Progressions/. An implementation is
  available at <https://github.com/statinf-otawa/otawa-clp>.
* The /Strided Interval/ (SI) domain from /WYSINWYX: What You See Is Not What
  You Execute/ and /Intermediate-Representation Recovery from Low-Level Code/.
* The /Wrapped Interval/ (WI) domain from /Signedness-Agnostic Program Analysis:
  Precise Integer Bounds for Low-Level Code/ (though this is stride-1).
* The /Signedness-Agnostic Strided Interval/ (SASI) from /BinTrimmer: Towards
  Static Binary Debloating Through Abstract Interpretation/. Implementation
  available at <https://github.com/ucsb-seclab/sasi>.
* Reduced products of congruence and (wrapped) interval domains, e.g., in Crab
  <https://github.com/seahorn/crab/blob/146f5399c72ff508f176e6392e490647ac657ce7/include/crab/domains/interval_congruence.hpp>.

A correctness specification of every operation is given in Cryptol in
@doc\/clp.cry@; the Haskell @correct_*@ predicates here mirror that
specification.
-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module What4.Domains.BV.CLP
  ( Clp
  , start
  , stride
  , n
  , mask
  , end
  , proper
  -- * Construction
  , mk
  -- , singleton
  -- , fromRange
  -- , fromFoldable
  -- * Conversion
  , toArith
  , fromArith
  , toBitwise
  , fromBitwise
  -- * Queries
  , member
  , toList
  -- , asSingleton
  -- , size
  -- , eq
  -- , ubounds
  -- , sbounds
  -- , ult
  -- , slt
  -- , overlap
  -- * Arithmetic
  , negate
  , add
  , sub
  , scale
  , mul
  , udiv
  , sdiv
  , urem
  , srem
  -- ** Arithmetic (SMT-LIB div-by-zero semantics)
  , udivSmtlib
  , uremSmtlib
  , sdivSmtlib
  , sremSmtlib
  -- * Bitwise operations
  , not
  , and
  , or
  , xor
  -- * Concatenation, extension, selection, and truncation
  , zext
  , sext
  , concat
  , select
  -- * Shifts and rotations
  , shl
  , lshr
  , ashr
  , rol
  , ror
  -- * Properties
  -- ** Generators
  , genClp
  , genElement
  , genPair
  -- ** Construction
  -- , correct_singleton
  -- ** Conversion
  , toArithCorrect
  , startEndArcCorrect
  , cosetArcCorrect
  , fromArithCorrect
  , roundtripArith
  , toBitwiseCorrect
  , fromBitwiseCorrect
  -- ** Internal helpers
  , modNegCorrect
  , modSubCorrect
  , firstCosetMemberCorrect
  , wrapOffsetCorrect
  , strideGcdDividesStride
  , strideGcdIsPow2
  , orbitLenViaToList
  , divByPow2Correct
  , invModPow2Correct
  , valueIndexCorrect
  , valueAtCorrect
  , circLeqAtZero
  , circLeqAnchorMin
  , circLeqAnchorMax
  , isSelfWrappingViaToList
  -- ** Queries
  -- , correct_asSingleton
  , startMember
  , endMember
  , toListMember
  , memberToList
  , toListNoDuplicates
  -- , correct_eq
  -- , correct_ubounds
  -- , correct_sbounds
  -- , correct_ult
  -- , correct_slt
  -- , correct_overlap
  -- ** Arithmetic
  , correct_neg
  , correct_add
  , correct_sub
  , correct_scale
  , correct_mul
  , correct_udiv
  , correct_sdiv
  , correct_urem
  , correct_srem
  -- *** Arithmetic (SMT-LIB div-by-zero semantics)
  , correct_udivSmtlib
  , correct_uremSmtlib
  , correct_sdivSmtlib
  , correct_sremSmtlib
  -- ** Bitwise operations
  , correct_not
  , correct_and
  , correct_or
  , correct_xor
  -- ** Concatenation, extension, selection, and truncation
  , correct_zero_ext
  , correct_sign_ext
  , correct_concat
  , correct_select
  -- ** Shifts and rotations
  , correct_shl
  , correct_lshr
  , correct_ashr
  , correct_rol
  , correct_ror
  ) where

import           Control.Exception (assert)
import           Data.Bits ((.&.), popCount, shiftL, shiftR)
import           GHC.TypeNats (Nat, type (+), type (<=))
import           Numeric.Natural (Natural)
import           Prelude hiding (negate, not, and, or, concat)
import qualified Prelude

import qualified Data.Bits as Bits
import qualified Data.Set as Set

import           Data.Parameterized.NatRepr (NatRepr, LeqProof(..), maxUnsigned)
import qualified Data.Parameterized.NatRepr as NR
import qualified What4.Domains.Arithmetic as Arith
import           What4.Domains.Arithmetic (countTrailingZerosOr0, isPow2Natural)
import qualified What4.Domains.BV.Arith as A
import qualified What4.Domains.BV.Bitwise as B
import           What4.Domains.Verification (Property, property, (==>), Gen, chooseInteger)

-- Note [Product abstraction]: A 'Clp' simultaneously over-approximates the
-- represented set in two complementary ways:
--
--   * /Algebraic/: \"the value lies in @start + g·Z@ mod @2^w@\", where
--     @g = gcd(stride, 2^w)@ is the lowest set bit of @stride@. Composes
--     analytically under the linear ops: closed-form result cosets are
--     available for negation, addition, scaling by a constant, multiplication,
--     and shifts by a constant.
--
--   * /Geometric/: \"the value lies on the arc walking forward from
--     @start@ to @end@\", i.e. the same convex/wrapped-interval view that
--     "What4.Domains.BV.Arith" tracks. Composes via 'toArith', the
--     corresponding @A@ operation, and 'fromArith'.
--
-- A CLP is /self-wrapping/ when its conceptual arc revolves past its own
-- @start@ before reaching @end@: the cumulative distance walked
-- @n · stride@ exceeds @2^w@, where @n@ is the step count from @start@ to
-- @end@. Self-wrapping is strictly stronger than \"crosses the @0/2^w-1@
-- boundary\" — a CLP can wrap around the number circle once without
-- self-wrapping (e.g. @{14, 0, 2}@ at width 4). See 'isSelfWrapping'.
--
-- For non-self-wrapping CLPs the triple @(start, end, stride)@ encodes both
-- views at once: the arc walking @start → end@ by @stride@ visits exactly the
-- coset elements in their natural cyclic order. The two views are coupled
-- and mutually refining at no extra cost.
--
-- When the conceptual orbit self-wraps, the two views /decouple/: the orbit
-- visits a partial subset of a full coset, but @(s, e, t)@ cannot
-- disambiguate \"arc length @L@\" from \"arc length @L + 2^w/g · stride@\".
-- We must commit to a representable shape. The best we can do is intersect:
-- take Arith's near-full convex arc and trim it to the result coset (see
-- 'selfWrappingResult'). This is strictly tighter than going through Arith
-- alone, which collapses stride to 1 and discards the coset.

-- | A 'Clp' represents the set
--
-- @
-- { (start + stride * i) mod (mask + 1) | 0 <= i <= n }
-- @
--
-- where @mask = 2^w - 1@ for some @w@. The orbit thus has @n + 1@ elements.
--
-- The conceptual /end/ of the orbit, @(start + n * stride) mod 2^w@, is
-- exposed via the 'end' accessor; see Note [Step-count representation] for
-- why @n@ is the primary field rather than @end@.
data Clp (w :: Nat)
  = Clp
    { start :: !Natural
    , stride :: !Natural
    , n :: !Natural
    , mask :: !Natural
    }
  deriving (Eq, Ord, Show)
-- Note [Step-count representation]: The CLP literature presents the domain as
-- a triple @(start, end, stride)@ where @end@ is a /value/ on the orbit. We
-- instead store the /step count/ @n@ — the index of the last orbit element,
-- with @end = (start + n·stride) mod 2^w@ derived on demand. The step count
-- is the more fundamental quantity for two reasons:
--
--   * /Self-wrapping is free/. A CLP self-wraps when @n·stride ≥ 2^w@,
--     which is an O(1) test in this representation. With @end@ as a value,
--     recovering @n@ requires modular inversion via 'invModPow2', i.e.
--     O(w log w).
--
--   * /Arithmetic stays branchless/. Sums and differences of orbits compose
--     additively in step counts: @n' = (n_a·t_a + n_b·t_b) / d@. With
--     @end@ as a value, distinguishing "arc length L" from "L + (2^w/g)·t",
--     once the conceptual orbit overruns its coset, requires committing to
--     a representable shape — see Note [Product abstraction].

-- | /O(w)/. The conceptual @end@ of the orbit: @(start + n * stride) mod 2^w@.
end :: Clp w -> Natural
end c@Clp{start, stride, n, mask} =
  assert (proper c) $ (start + n * stride) .&. mask
{-# INLINE end #-}

-- | The data-structure invariants of 'Clp'.
proper :: Clp w -> Bool
proper Clp {start, stride, n, mask} =
  let g = lowestSetBit stride
      orbit = orbitLenOf mask g
  in Prelude.and
     [ start .&. mask == start
     , stride .&. mask == stride
     , stride > 0
     , n < orbit
     -- Singletons (@n = 0@) are canonicalized to stride 1.
     , n /= 0 || stride == 1
     -- Full cosets (@n + 1 = orbit@): smallest start in coset, stride = @g@.
     , n + 1 < orbit || (start < g && stride == g)
     ]

-- ------------------------------------------------------------------
-- * Internal helpers

integerToNatural :: Integer -> Natural
integerToNatural = fromIntegral
{-# INLINE integerToNatural #-}

-- | /O(w)/. Reduce a 'Natural' modulo @2^w@, where @w@ is the width of the CLP.
modMask :: Clp w -> Natural -> Natural
modMask c v = assert (proper c) $ v .&. mask c
{-# INLINE modMask #-}

-- | /O(w)/. Modular additive inverse modulo @mask + 1@.
modNeg :: Natural -> Natural -> Natural
modNeg mask x =
  assert ((mask + 1) .&. mask == 0) $
  assert (x .&. mask == x) $
  (mask + 1 - x) .&. mask
{-# INLINE modNeg #-}

-- | /O(w)/. Modular subtraction @x - y@ mod @mask + 1@.
modSub :: Natural -> Natural -> Natural -> Natural
modSub mask x y =
  assert ((mask + 1) .&. mask == 0) $
  assert (x .&. mask == x) $
  assert (y .&. mask == y) $
  (x + modNeg mask y) .&. mask
{-# INLINE modSub #-}

-- | /O(w)/. The wrap-around offset of @v@ from @start@: @(v - start) mod 2^w@.
wrapOffset :: Clp w -> Natural -> Natural
wrapOffset c@Clp{start, mask} v =
  assert (proper c) $ modSub mask v start
{-# INLINE wrapOffset #-}

-- | /O(1)/. The lowest set bit of @x@; equivalently @gcd(x, 2^w)@ for any
-- @w@ at least the bit-length of @x@.
lowestSetBit :: Natural -> Natural
lowestSetBit x = 1 `shiftL` countTrailingZerosOr0 (toInteger x)
{-# INLINE lowestSetBit #-}

-- | /O(1)/. @gcd(stride, 2^w)@. Since @2^w@ is a power of two, this equals the
-- lowest set bit of @stride@.
strideGcd :: Clp w -> Natural
strideGcd Clp{stride} = lowestSetBit stride
{-# INLINE strideGcd #-}

-- | /O(w)/. @2^w \/ g@, where @mask = 2^w - 1@ and @g@ is a power-of-two
-- divisor of @2^w@ (e.g. @gcd(stride, 2^w)@). Used to compute the orbit
-- length of a CLP from raw @mask@ and @g@ before a 'Clp' value exists.
orbitLenOf :: Natural -> Natural -> Natural
orbitLenOf mask g =
  assert (isPow2Natural (mask + 1)) $
  (mask + 1) `divByPow2` g
{-# INLINE orbitLenOf #-}

-- | /O(w)/. The orbit length: the number of distinct bitvectors visited by
-- the progression, which is @2^w \/ gcd(stride, 2^w)@. See
-- 'orbitLenViaToList'.
orbitLen :: Clp w -> Natural
orbitLen c@Clp{mask} = orbitLenOf mask (strideGcd c)
{-# INLINE orbitLen #-}

-- | /O(w)/. The smallest value @v@ in the wrapped arc starting at @lo@
-- (i.e. @v = (lo + off) mod 2^w@ for some @off ≥ 0@) with @v ≡ x (mod g)@,
-- where @g@ is a power-of-two divisor of @2^w = mask + 1@.
firstCosetMember ::
  Natural {- ^ @mask = 2^w - 1@ -} ->
  Natural {- ^ @lo@ -} ->
  Natural {- ^ @g@ -} ->
  Natural {- ^ @x@ -} ->
  Natural
-- The offset @off@ is @(x - lo) mod g@, taken on the @g@-cycle: since @g@
-- divides @2^w@, masking by @g - 1@ after a mod-@2^w@ subtraction yields
-- the mod-@g@ residue.
firstCosetMember mask lo g x =
  assert (isPow2Natural g && (mask + 1) `mod` g == 0) $
  (lo + (modSub mask x lo .&. (g - 1))) .&. mask
{-# INLINE firstCosetMember #-}

-- | /O(w)/. @x \/ p@ where @p@ is a power of two, computed as a right shift.
-- Asserts that @p@ is a (nonzero) power of two.
divByPow2 :: Natural -> Natural -> Natural
divByPow2 x p =
  assert (isPow2Natural p) $ x `shiftR` popCount (p - 1)
{-# INLINE divByPow2 #-}

-- | /O(w log w)/. Modular inverse of @a@ modulo @m@ where @m@ is a power of two
-- and @a@ is odd.
invModPow2 :: Natural -> Natural -> Natural
-- Computed via Hensel lifting (Newton iteration): @x' = x * (2 - a*x) mod m@.
-- Each step doubles the number of correct low bits, so the loop runs in @O(log
-- w)@ iterations of @O(w)@ work.
invModPow2 a m = assert (a .&. 1 == 1) $ go 1
  where
    mMinus1 = m - 1
    go x =
      let ax = (a * x) .&. mMinus1 in
      if ax == 1
        then x
        else go ((x * (2 + m - ax)) .&. mMinus1)

-- | /O(w log w)/. The progression index of @v@: the unique @i@ in @[0, 2^w \/
-- g)@ such that @start + i*stride ≡ v (mod 2^w)@, where @g = gcd(stride, 2^w)@.
-- Requires @g@ to divide @(v - start) mod 2^w@.
--
-- This costs O(w log w) for the modular inverse via 'invModPow2'; the step
-- count of the CLP itself, @n c@, is available directly.
valueIndex :: Clp w -> Natural -> Natural
valueIndex c@Clp{stride, mask} v =
  assert (proper c) $
  assert (off .&. (g - 1) == 0) $
  ((off `divByPow2` g) * sInv) .&. (m' - 1)
  where
    -- @g@ is a power of two (see 'strideGcd'), so all divisions by it (and by
    -- @2^w@) are right shifts.
    off  = wrapOffset c v
    g    = strideGcd c
    m'   = (mask + 1) `divByPow2` g
    sInv = invModPow2 (stride `divByPow2` g) m'

-- | /O(w)/. The value at progression index @i@: @(start + i * stride) mod 2^w@.
-- Left inverse of 'valueIndex' on indices in @[0, 2^w \/ g)@.
valueAt :: Clp w -> Natural -> Natural
valueAt c@Clp{start, stride} i = assert (proper c) $
  modMask c (start + i * stride)
{-# INLINE valueAt #-}

-- | /O(w)/. SASI and WI's @≤_x@: @a ≤_x b@ iff @(a - x) mod 2^w <= (b - x) mod
-- 2^w@. Equivalently, traversing the circle of bitvectors starting at @x@, @a@
-- is reached no later than @b@.
circLeq :: Natural -> Natural -> Natural -> Natural -> Bool
circLeq m x a b = (a + nx) .&. m <= (b + nx) .&. m
  where nx = modNeg m x

-- | /O(1)/. Does this CLP self-wrap? A CLP is self-wrapping if the
-- cumulative distance traversed by its orbit (@n * stride@, where @n@ is the
-- number of steps from @start@ to @end@) exceeds @2^w@. Geometrically: walking
-- around the number circle from @start@, the orbit passes its starting point
-- at least once before reaching @end@.
--
-- Note that all CLP values are distinct by construction (any orbit of length
-- @≤ 2^w \/ gcd(stride, 2^w)@), so self-wrapping does /not/ mean residue
-- classes repeat. It only describes how far the orbit traveled.
isSelfWrapping :: Clp w -> Bool
isSelfWrapping Clp{stride, n, mask} = n * stride > mask
{-# INLINE isSelfWrapping #-}

-- ------------------------------------------------------------------
-- * Construction

-- | Construct a CLP from @(start, stride, n)@: the orbit
-- @{ start, start + stride, ..., start + n·stride }@ (all mod @2^w@).
-- Asserts that @start@ and @stride@ fit in @w@ bits, that @stride > 0@, that
-- @n@ is within the orbit length @2^w \/ gcd(stride, 2^w)@, and that the
-- resulting CLP is 'proper'.
--
-- Saturates and canonicalizes:
--
--   * @n = 0@ (singleton): stride is forced to 1.
--   * @n + 1 = 2^w \/ g@ (full coset): @start@ is reduced to its residue
--     modulo @g@, stride is reduced to @g@.
mk ::
  NatRepr w ->
  -- | @start@
  Natural ->
  -- | @stride@
  Natural ->
  -- | @n@: step count, @0 ≤ n < 2^w \/ gcd(stride, 2^w)@
  Natural ->
  Clp w
mk w s st nn =
  assert (s .&. m == s) $
  assert (st .&. m == st) $
  assert (st > 0) $
  assert (nn < orbit) $
  assert (proper c) c
  where
    m = integerToNatural (maxUnsigned w)
    g = lowestSetBit st
    orbit = orbitLenOf m g
    (s', st', n')
      -- Singleton: stride is irrelevant; pin to 1.
      | nn == 0          = (s, 1, 0)
      -- Full coset: any element of @start mod g + g·Z@ is a valid start.
      -- Pick @start = start mod g@, @stride = g@.
      | nn + 1 == orbit  = (s .&. (g - 1), g, orbit - 1)
      | otherwise        = (s, st, nn)
    c = Clp { start = s', stride = st', n = n', mask = m }
{-# INLINE mk #-}

-- ------------------------------------------------------------------
-- * Conversion

-- | /O(w)/. Convert a CLP to an arithmetic domain (wrapped interval).
--
-- For non-self-wrapping CLPs, the result is the interval @[start, end]@
-- (over-approximating by collapsing to stride = 1). For self-wrapping CLPs,
-- the orbit visits exactly the values congruent to @start@ modulo
-- @g = gcd(stride, 2^w)@, so we use the tightest such interval:
-- @[start \`mod\` g, mask + 1 - g + (start \`mod\` g)]@.
toArith :: Clp w -> A.Domain w
-- For self-wrapping CLPs, this does not yield the tightest interval
-- that contains all of their points. By the three-gap theorem (Sós 1957,
-- Świerczkowski 1958, Van Ravenstein 1988), that interval would be the
-- complement of the largest gap between elements. This is computable via
-- Ostrowski-decomposition and was implemented previously, but removed as it was
-- very complex. You can find it in the git history if you need it.
toArith c = if isSelfWrapping c then cosetArc c else startEndArc c

-- | /O(w)/. The arc @[start, ..., end]@ on the number circle, ignoring stride.
-- The convex hull (in the wrapped-interval sense) of a non-self-wrapping orbit;
-- under-approximates a self-wrapping orbit, so caller must ensure the input
-- is not self-wrapping.
startEndArc :: Clp w -> A.Domain w
startEndArc c@Clp{start = s, stride = t, n = nn, mask = m} =
  assert (proper c) $
  assert (Prelude.not (isSelfWrapping c)) $
  -- Non-self-wrapping: @n·stride < 2^w@, so the arc length is exactly @n·t@.
  A.interval (toInteger m) (toInteger s) (toInteger (nn * t))

-- | /O(w)/. The arc @[start \`mod\` g, ..., start \`mod\` g + (2^w - g)]@,
-- where @g = gcd(stride, 2^w)@. The union of all bitvectors congruent to
-- @start@ modulo @g@; sound on any CLP, but only a tight cover on
-- self-wrapping orbits, so caller must ensure the input is self-wrapping.
cosetArc :: Clp w -> A.Domain w
cosetArc c@Clp{start = s, mask = m} =
  assert (proper c) $
  assert (isSelfWrapping c) $
  let g = strideGcd c
      imask = toInteger m
      lo = toInteger (s .&. (g - 1))
  in A.interval imask lo (imask + 1 - toInteger g)

-- | /O(w)/. Convert an arithmetic domain (wrapped interval) to a CLP.
fromArith :: NatRepr w -> A.Domain w -> Maybe (Clp w)
fromArith w = \case
  A.BVDAny _mask -> Just (mk w 0 1 (integerToNatural imask))
    where imask = maxUnsigned w
  d | A.isBottom d -> Nothing
    | otherwise -> case A.arithDomainData d of
        Nothing -> Nothing
        Just (lo, sz) -> Just (mk w (integerToNatural lo) 1 (integerToNatural sz))

-- TODO: The arith<->bitwise helpers below duplicate
-- 'arithToBitwiseDomain'/'bitwiseToArithDomain' in "What4.Domains.BV". Once
-- those are moved into a common module that 'CLP' can import (e.g. by adding a
-- dep from 'BV.Bitwise' to 'BV.Arith'), inline-call them instead.

-- TODO? Can we do better than just arith-to-bitwise by considering stride?

-- | /O(w log w)/. Convert a CLP to a bitwise domain.
toBitwise :: Clp w -> B.Domain w
toBitwise c = arithToBitwise (toArith c)
  where
    arithToBitwise a =
      let imask = A.bvdMask a in
      case A.arithDomainData a of
        Nothing -> B.interval imask 0 imask
        Just (alo, _) -> B.interval imask lo hi
          where
            u = A.unknowns a
            hi = alo Bits..|. u
            lo = hi `Bits.xor` u

-- | /O(1)/. Convert a bitwise domain to a CLP.
fromBitwise :: NatRepr w -> B.Domain w -> Maybe (Clp w)
fromBitwise w b = fromArith w (bitwiseToArith b)
  where
    bitwiseToArith d =
      let imask = B.bvdMask d
          (lo, hi) = B.bitbounds d
      in A.interval imask lo ((hi - lo) Bits..&. imask)

-- ------------------------------------------------------------------
-- * Queries

-- | /O(w log w)/. Test if the given value is a member of the CLP.
member :: Clp w -> Natural -> Bool
-- References:
--
-- * SASI Definition 3, Membership function
--
-- SASI\'s @member@ function is actually broken. Their concretization function
-- matches our 'toList', which means that their intervals can semantically
-- support wrapping around multiple times, but their membership function only
-- supports non-self-wrapping intervals. This is likely due to its heritage
-- from Wrapped Intervals, where self-wrapping stride-1 intervals would result
-- in saturation.
member c v = assert (proper c) $
  wrapOffset c v `mod` strideGcd c == 0
  && valueIndex c v <= n c

-- | /O(2^w \/ g)/, where @g = gcd(stride, 2^w)@. Enumerate the (distinct)
-- elements of a CLP, in the order they are produced by the progression:
-- @start, start + stride, ..., end@ (all mod @2^w@).
toList :: Clp w -> [Natural]
-- References:
--
-- * CLP Section 3, @conc@
-- * SASI Definition 1, Concretization function
toList c@Clp{start, stride, n} = assert (proper c) $ go 0 start
  where
    go !i !v
      | i == n    = [v]
      | otherwise = v : go (i + 1) (modMask c (v + stride))

-- ------------------------------------------------------------------
-- * Lifted operations

-- These helpers convert a CLP to an arithmetic or bitwise domain, apply the
-- corresponding operation there, and convert back. Since the result of an
-- @A.*@ or @B.*@ op on a proper input is always proper (never bottom),
-- @fromArith@\/@fromBitwise@ here always succeed, and we project from the
-- 'Maybe' with 'fromJustUnsafe'. This loses precision (the round-trip
-- collapses non-trivial strides), but is sound.

fromJustUnsafe :: String -> Maybe a -> a
fromJustUnsafe loc = \case
  Just x  -> x
  Nothing -> error ("What4.Domains.BV.CLP: " ++ loc ++ ": Nothing")
{-# INLINE fromJustUnsafe #-}

liftArith1 ::
  (1 <= w) =>
  NatRepr w ->
  (A.Domain w -> A.Domain w) ->
  Clp w -> Clp w
liftArith1 w f c =
  fromJustUnsafe "liftArith1" (fromArith w (f (toArith c)))
{-# INLINE liftArith1 #-}

liftArith2 ::
  (1 <= w) =>
  NatRepr w ->
  (A.Domain w -> A.Domain w -> A.Domain w) ->
  Clp w -> Clp w -> Clp w
liftArith2 w f a b =
  fromJustUnsafe "liftArith2" (fromArith w (f (toArith a) (toArith b)))
{-# INLINE liftArith2 #-}

liftBitwise1 ::
  (1 <= w) =>
  NatRepr w ->
  (B.Domain w -> B.Domain w) ->
  Clp w -> Clp w
liftBitwise1 w f c =
  fromJustUnsafe "liftBitwise1" (fromBitwise w (f (toBitwise c)))
{-# INLINE liftBitwise1 #-}

liftBitwise2 ::
  (1 <= w) =>
  NatRepr w ->
  (B.Domain w -> B.Domain w -> B.Domain w) ->
  Clp w -> Clp w -> Clp w
liftBitwise2 w f a b =
  fromJustUnsafe "liftBitwise2" (fromBitwise w (f (toBitwise a) (toBitwise b)))
{-# INLINE liftBitwise2 #-}

-- ------------------------------------------------------------------
-- * Arithmetic

-- | /O(w)/. Negation: stride is preserved; the orbit reverses, so the new
-- @start@ is the old @end@ negated. The step count @n@ is unchanged.
negate :: (1 <= w) => NatRepr w -> Clp w -> Clp w
negate w c@Clp{stride, n = nn, mask} =
  assert (proper c) $
  mk w (modNeg mask (end c)) stride nn

-- | /O(w)/. Addition.
add :: (1 <= w) => NatRepr w -> Clp w -> Clp w -> Clp w
-- References:
--
-- * CLP 4.2 Arithmetic Operations
-- * WI 3.2 Analysing expressions
--
-- In the CLP (start, end, stride) formulation, they give:
--
--   (l1, u1, δ1) + (l2, u2, δ2) := (l1 + l2, u1 + u2, gcd(δ1, δ2))
--
-- Shift each orbit by the other's @start@, then walk
-- @n a · stride a + n b · stride b@ steps from @start a + start b@ in stride
-- @d = gcd(stride a, stride b)@ (with singleton operands skipped). When the
-- conceptual arc self-wraps, fall back to intersecting Arith's near-full arc
-- with the @g@-coset (see 'arithMeetCoset').
add w a b =
  assert (proper a) $
  assert (proper b) $
  if span_ >= mask a + 1
    then arithMeetCoset w (A.add (toArith a) (toArith b)) d start'
    else mk w start' d (span_ `div` d)
  where
    d      = strideGcd2 a b
    span_  = n a * stride a + n b * stride b
    start' = modMask a (start a + start b)

-- | /O(w)/. Subtraction.
sub :: (1 <= w) => NatRepr w -> Clp w -> Clp w -> Clp w
sub w a b =
  assert (proper a) $
  assert (proper b) $
  if span_ >= mask a + 1
    then arithMeetCoset w (A.add (toArith a) (A.negate (toArith b))) d start'
    else mk w start' d (span_ `div` d)
  where
    d      = strideGcd2 a b
    span_  = n a * stride a + n b * stride b
    start' = modSub (mask a) (start a) (end b)

-- | Result stride for 'add'\/'sub': @gcd(stride a, stride b)@, with singleton
-- operands skipped (their stride is the dummy value @1@, which would otherwise
-- collapse the result stride).
strideGcd2 :: Clp w -> Clp w -> Natural
strideGcd2 a b = case (n a, n b) of
  (0, 0) -> 1
  (0, _) -> stride b
  (_, 0) -> stride a
  _      -> Prelude.gcd (stride a) (stride b)

-- | The CLP whose elements are exactly those of @arith@ that lie in the
-- @g@-coset of @start'@, where @g = lowestSetBit d@. Used by 'add'\/'sub'
-- when the conceptual arc self-wraps: strictly tighter than @liftArith2 A.add@
-- when @g > 1@, since stride stays @g@ rather than collapsing to 1. See
-- Note [Product abstraction].
arithMeetCoset ::
  (1 <= w) =>
  NatRepr w ->
  -- | The Arith arc to restrict.
  A.Domain w ->
  -- | Result stride @d@: must be positive and at most @2^w - 1@.
  Natural ->
  -- | @start'@: any representative of the target coset.
  Natural ->
  Clp w
arithMeetCoset w arith d start' =
  assert (d > 0 && d <= m) $
  case A.arithDomainData arith of
    -- Arith is full: result is the full @g@-coset of @start'@. Let 'mk'
    -- canonicalize (it reduces @start@ to its residue mod @g@).
    Nothing -> mk w start' d (orbitLenOf m g - 1)
    Just (lo, sz) ->
      let lo'    = fromInteger lo
          sz'    = fromInteger sz
          clpLo  = firstCosetMember m lo' g start'
          off    = modSub m clpLo lo'
          nSteps = divByPow2 (sz' - off) g
      in mk w clpLo g nSteps
  where
    m = integerToNatural (maxUnsigned w)
    g = lowestSetBit d

scale :: (1 <= w) => NatRepr w -> Integer -> Clp w -> Clp w
scale w k = liftArith1 w (A.scale k)

-- | The effective @(lo, stride)@ pair used by 'mul' for the result-stride
-- formula. Singletons contribute stride 0 (their orbit has no nontrivial
-- differences).
effLoStride :: Clp w -> (Natural, Natural)
effLoStride c
  | n c == 0  = (start c, 0)
  | otherwise = (start c, stride c)

-- | /O(w)/. Multiplication.
mul :: (1 <= w) => NatRepr w -> Clp w -> Clp w -> Clp w
-- References:
--
-- * CLP 4.2 Arithmetic Operations
--
-- In the CLP (start, end, stride) formulation, they give:
-- 
--   (l1, u1, δ1) ∗ (l2, u2, δ2) :=
--     ( min(l1 ∗ l2, u1 ∗ u2, l1 ∗ u2, u1 ∗ l2)
--     , max(l1 ∗ l2, u1 ∗ u2, l1 ∗ u2, u1 ∗ l2)
--     , gcd(|l1 ∗ δ2|, |l2 ∗ δ1|, δ1 ∗ δ2)
--     )
--
-- Note that WI 3.2 Analysing expressions has a significantly more complex
-- definition of multiplication that splits the intervals at the poles, does
-- piecewise signed/unsigned multiplication, and joins the results. This may be
-- more precise, and we might want to implement it in the future.
--
-- The product set's stride (in @Z\/2^w@) is generated by
-- @gcd(l1·t2, l2·t1, t1·t2)@: those are the stepwise differences that arise
-- when one factor is held fixed and the other steps once (the @t1·t2@ term
-- comes from stepping both). Bounds come from 'A.mul' (signed-corner
-- cross-products via 'A.zbounds'); we then refine to the gcd coset via
-- 'arithMeetCoset'.
mul w a b =
  assert (proper a) $
  assert (proper b) $
  if dMod == 0
    then mk w start' 1 0
    else arithMeetCoset w (A.mul (toArith a) (toArith b)) dMod start'
  where
    (l1, t1) = effLoStride a
    (l2, t2) = effLoStride b
    dInt   = Prelude.gcd (l1 * t2) (Prelude.gcd (l2 * t1) (t1 * t2))
    dMod   = dInt .&. mask a
    start' = modMask a (start a * start b)

udiv :: (1 <= w) => NatRepr w -> Clp w -> Clp w -> Clp w
udiv w = liftArith2 w A.udiv

urem :: (1 <= w) => NatRepr w -> Clp w -> Clp w -> Clp w
urem w = liftArith2 w A.urem

sdiv :: (1 <= w) => NatRepr w -> Clp w -> Clp w -> Clp w
sdiv w = liftArith2 w (A.sdiv w)

srem :: (1 <= w) => NatRepr w -> Clp w -> Clp w -> Clp w
srem w = liftArith2 w (A.srem w)

-- ------------------------------------------------------------------
-- ** Arithmetic (SMT-LIB div-by-zero semantics)

udivSmtlib :: (1 <= w) => NatRepr w -> Clp w -> Clp w -> Clp w
udivSmtlib w = liftArith2 w A.udivSmtlib

uremSmtlib :: (1 <= w) => NatRepr w -> Clp w -> Clp w -> Clp w
uremSmtlib w = liftArith2 w A.uremSmtlib

sdivSmtlib :: (1 <= w) => NatRepr w -> Clp w -> Clp w -> Clp w
sdivSmtlib w = liftArith2 w (A.sdivSmtlib w)

sremSmtlib :: (1 <= w) => NatRepr w -> Clp w -> Clp w -> Clp w
sremSmtlib w = liftArith2 w (A.sremSmtlib w)

-- ------------------------------------------------------------------
-- * Bitwise operations

not :: (1 <= w) => NatRepr w -> Clp w -> Clp w
not w = liftBitwise1 w B.not

and :: (1 <= w) => NatRepr w -> Clp w -> Clp w -> Clp w
and w = liftBitwise2 w B.and

or :: (1 <= w) => NatRepr w -> Clp w -> Clp w -> Clp w
or w = liftBitwise2 w B.or

xor :: (1 <= w) => NatRepr w -> Clp w -> Clp w -> Clp w
xor w = liftBitwise2 w B.xor

-- ------------------------------------------------------------------
-- * Concatenation, extension, selection, and truncation

zext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Clp w -> NatRepr u -> Clp u
zext _w c u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      fromJustUnsafe "zext" (fromArith u (A.zext (toArith c) u))

sext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Clp w -> NatRepr u -> Clp u
sext w c u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      fromJustUnsafe "sext" (fromArith u (A.sext w (toArith c) u))

concat ::
  forall u v.
  (1 <= u, 1 <= v) =>
  NatRepr u -> Clp u -> NatRepr v -> Clp v -> Clp (u + v)
concat u a v b =
  case NR.leqAddPos u v of
    LeqProof ->
      fromJustUnsafe "concat"
        (fromArith (NR.addNat u v) (A.concat u (toArith a) v (toArith b)))

select ::
  forall i n w.
  (1 <= n, 1 <= w, i + n <= w) =>
  NatRepr i -> NatRepr n -> NatRepr w -> Clp w -> Clp n
select i n _w c =
  fromJustUnsafe "select" (fromArith n (A.select i n (toArith c)))

-- ------------------------------------------------------------------
-- * Shifts and rotations

shl :: (1 <= w) => NatRepr w -> Clp w -> Clp w -> Clp w
shl w = liftArith2 w (A.shl w)

lshr :: (1 <= w) => NatRepr w -> Clp w -> Clp w -> Clp w
lshr w = liftArith2 w (A.lshr w)

ashr :: (1 <= w) => NatRepr w -> Clp w -> Clp w -> Clp w
ashr w = liftArith2 w (A.ashr w)

rol :: (1 <= w) => NatRepr w -> Clp w -> Clp w -> Clp w
rol w = liftBitwise2 w (B.rolAbstract w)

ror :: (1 <= w) => NatRepr w -> Clp w -> Clp w -> Clp w
ror w = liftBitwise2 w (B.rorAbstract w)

-- ------------------------------------------------------------------
-- * Generators

-- | Generator for a proper 'Clp' at width @w@.
genClp :: NatRepr w -> Gen (Clp w)
genClp w = do
  let m = integerToNatural (maxUnsigned w)
  s <- integerToNatural <$> chooseInteger (0, toInteger m)
  -- Stride must be in @[1, 2^w - 1]@; we pick from @[1, 2^w]@ and clamp by mask
  -- so that stride is uniformly distributed over [1, 2^w-1] (a stride of 2^w
  -- mod mask = 0 would be improper).
  st <- integerToNatural <$> chooseInteger (1, toInteger m)
  -- Pick a step count @i@ in @[0, orbit)@, where @orbit = 2^w \/ g@ and
  -- @g = gcd(stride, 2^w)@.
  let g = st .&. ((m + 1) - st)
  let orbit = (m + 1) `divByPow2` g
  i <- integerToNatural <$> chooseInteger (0, toInteger orbit - 1)
  pure (mk w s st i)

-- | Generate a random element of the given (proper) CLP.
genElement :: Clp w -> Gen Natural
genElement c = do
  i <- integerToNatural <$> chooseInteger (0, toInteger (n c))
  pure (valueAt c i)

-- | Generate a random CLP and an element contained in it.
genPair :: NatRepr w -> Gen (Clp w, Natural)
genPair w = do
  c <- genClp w
  x <- genElement c
  pure (c, x)

-- ------------------------------------------------------------------
-- * Correctness properties

-- ------------------------------------------------------------------
-- ** Internal helpers

-- | @x + modNeg (2^k - 1) x ≡ 0 (mod 2^k)@.
modNegCorrect :: Natural -> Int -> Property
modNegCorrect x k =
  k >= 1 ==> property ((x' + modNeg m x') .&. m == 0)
  where
    m  = (1 `shiftL` k) - 1
    x' = x .&. m

-- | @modSub (2^k - 1) x y + y ≡ x (mod 2^k)@.
modSubCorrect :: Natural -> Natural -> Int -> Property
modSubCorrect x y k =
  k >= 1 ==> property ((modSub m x' y' + y') .&. m == x')
  where
    m  = (1 `shiftL` k) - 1
    x' = x .&. m
    y' = y .&. m

-- | At width @k@ with @g = 2^j@ (@j ≤ k@): the result @v = firstCosetMember
-- (2^k - 1) lo g x@ is in the @g@-coset of @x@ (i.e. @(v - x) mod g == 0@),
-- and the wrap-around offset @(v - lo) mod 2^k@ is less than @g@ (so @v@ is
-- the /first/ such value at or after @lo@ on the wrapped arc).
firstCosetMemberCorrect :: Natural -> Natural -> Int -> Int -> Property
firstCosetMemberCorrect lo x k j =
  k >= 1 ==> j >= 0 ==> j <= k ==>
    property ((modSub m v x' .&. (g - 1) == 0)
           && (modSub m v lo' < g))
  where
    m   = (1 `shiftL` k) - 1
    g   = 1 `shiftL` j
    lo' = lo .&. m
    x'  = x .&. m
    v   = firstCosetMember m lo' g x'

-- | @start + wrapOffset c v ≡ v (mod 2^w)@.
wrapOffsetCorrect :: Clp w -> Natural -> Property
wrapOffsetCorrect c v =
  proper c ==>
    property (modMask c (start c + wrapOffset c v) == modMask c v)

-- | @strideGcd c@ divides @stride c@ and divides @2^w@.
strideGcdDividesStride :: Clp w -> Property
strideGcdDividesStride c =
  proper c ==>
    property (stride c `mod` strideGcd c == 0
           && (mask c + 1) `mod` strideGcd c == 0)

-- | @strideGcd c@ is a power of two (i.e. @g .&. (g - 1) == 0@).
strideGcdIsPow2 :: Clp w -> Property
strideGcdIsPow2 c =
  proper c ==> property (g > 0 && g .&. (g - 1) == 0)
  where g = strideGcd c

-- | 'orbitLen' upper-bounds the length of 'toList': it equals the number of
-- distinct values reachable from @start@ by stepping by @stride@, while
-- 'toList' stops early at @end@.
orbitLenViaToList :: Clp w -> Property
orbitLenViaToList c =
  proper c ==> property (fromIntegral (length (toList c)) <= orbitLen c)

-- | @divByPow2 (q * 2^k) (2^k) == q@.
divByPow2Correct :: Natural -> Int -> Property
divByPow2Correct q k =
  k >= 0 ==> property (divByPow2 (q * p) p == q)
  where p = 1 `shiftL` k

-- | @(a * invModPow2 a (2^k)) ≡ 1 (mod 2^k)@ for odd @a@ and @k >= 1@.
invModPow2Correct :: Natural -> Int -> Property
invModPow2Correct a k =
  k >= 1 ==> a `mod` 2 == 1 ==>
    property ((a * invModPow2 a m) `mod` m == 1)
  where m = 1 `shiftL` k

-- | @valueAt c (valueIndex c v) ≡ v (mod 2^w)@ whenever @v@ is on the
-- progression (i.e. @strideGcd c@ divides @wrapOffset c v@).
valueIndexCorrect :: Clp w -> Natural -> Property
valueIndexCorrect c v =
  proper c ==> wrapOffset c v' `mod` strideGcd c == 0 ==>
    property (valueAt c (valueIndex c v') == v')
  where v' = modMask c v

-- | @valueIndex c (valueAt c i) == i@ for any @i@ in @[0, orbitLen c)@.
valueAtCorrect :: Clp w -> Natural -> Property
valueAtCorrect c i =
  proper c ==>
    let i' = i `mod` orbitLen c in
    property (valueIndex c (valueAt c i') == i')

-- | @circLeq m 0@ degenerates to ordinary unsigned @<=@.
circLeqAtZero :: Natural -> Natural -> Int -> Property
circLeqAtZero a b k =
  k >= 1 ==> property (circLeq m 0 a' b' == (a' <= b'))
  where
    m  = (1 `shiftL` k) - 1
    a' = a .&. m
    b' = b .&. m

-- | The anchor @x@ is the minimum: @circLeq m x x v@ always holds.
circLeqAnchorMin :: Natural -> Natural -> Int -> Property
circLeqAnchorMin x v k =
  k >= 1 ==> property (circLeq m (x .&. m) (x .&. m) (v .&. m))
  where m = (1 `shiftL` k) - 1

-- | The predecessor of @x@ is the maximum: @circLeq m x v (x - 1)@ always holds.
circLeqAnchorMax :: Natural -> Natural -> Int -> Property
circLeqAnchorMax x v k =
  k >= 1 ==>
    property (circLeq m x' (v .&. m) ((x' + m) .&. m))
  where
    m  = (1 `shiftL` k) - 1
    x' = x .&. m

-- | 'isSelfWrapping' agrees with the orbit length: a CLP is self-wrapping iff
-- stepping through every element of 'toList' travels strictly more than @2^w@
-- in total. Concretely, @isSelfWrapping c@ iff
-- @(length (toList c) - 1) * stride > 2^w - 1@.
isSelfWrappingViaToList :: Clp w -> Property
isSelfWrappingViaToList c@Clp{stride, mask} =
  proper c ==> property (isSelfWrapping c == (k * stride > mask))
  where
    k = fromIntegral (length (toList c) - 1) :: Natural

-- ------------------------------------------------------------------
-- ** Queries

-- | A CLP always contains its own @start@.
startMember :: Clp w -> Property
startMember c = proper c ==> property (member c (start c))

-- | A CLP always contains its own @end@.
endMember :: Clp w -> Property
endMember c = proper c ==> property (member c (end c))

-- | Every element produced by 'toList' is a member of the CLP.
toListMember :: Clp w -> Property
toListMember c =
  proper c ==> property (Prelude.all (member c) (toList c))

-- | If 'member' returns 'True' for some bitvector @x@, then @x@ appears in
-- 'toList'.
memberToList :: Clp w -> Natural -> Property
memberToList c x =
  proper c ==> (member c x' ==> property (x' `elem` toList c))
  where x' = modMask c x

-- | 'toList' produces no duplicate elements.
toListNoDuplicates :: Clp w -> Property
toListNoDuplicates c = proper c ==> property (noDuplicates (toList c))
  where
    noDuplicates xs = length xs == Set.size (Set.fromList xs)

-- ------------------------------------------------------------------
-- ** Conversion

-- | Every element in a CLP is also in its 'toArith' conversion.
toArithCorrect :: (1 <= w) => NatRepr w -> Clp w -> Natural -> Property
toArithCorrect _w c x =
  proper c ==> member c x' ==>
    property (A.member (toArith c) (toInteger x'))
  where
    x' = modMask c x

-- | On non-self-wrapping CLPs, every orbit member lies in 'startEndArc'.
startEndArcCorrect :: (1 <= w) => NatRepr w -> Clp w -> Natural -> Property
startEndArcCorrect _w c x =
  proper c ==> Prelude.not (isSelfWrapping c) ==> member c x' ==>
    property (A.member (startEndArc c) (toInteger x'))
  where
    x' = modMask c x

-- | On self-wrapping CLPs, every orbit member lies in 'cosetArc'.
cosetArcCorrect :: (1 <= w) => NatRepr w -> Clp w -> Natural -> Property
cosetArcCorrect _w c x =
  proper c ==> isSelfWrapping c ==> member c x' ==>
    property (A.member (cosetArc c) (toInteger x'))
  where
    x' = modMask c x

-- | Every element in an arithmetic domain is also in its 'fromArith' conversion
-- (when that conversion produces a CLP).
fromArithCorrect :: (1 <= w) => NatRepr w -> A.Domain w -> Integer -> Property
fromArithCorrect w a x =
  A.proper w a ==> A.member a x ==>
    case fromArith w a of
      Nothing -> property True
      Just c -> property (member c (integerToNatural (x .&. maxUnsigned w)))

-- | Converting from Arith to CLP and back is exact: the round-tripped domain
-- contains exactly the same elements as the original.
roundtripArith :: (1 <= w) => NatRepr w -> A.Domain w -> Integer -> Property
roundtripArith w a x =
  A.proper w a ==>
    case fromArith w a of
      Nothing -> property True
      Just c -> property (A.member a x == A.member (toArith c) x)

-- | Every element in a CLP is also in its 'toBitwise' conversion.
toBitwiseCorrect :: (1 <= w) => NatRepr w -> Clp w -> Natural -> Property
toBitwiseCorrect _w c x =
  proper c ==> member c x' ==>
    property (B.member (toBitwise c) (toInteger x'))
  where
    x' = modMask c x

-- | Every element in a bitwise domain is also in its 'fromBitwise' conversion
-- (when that conversion produces a CLP).
fromBitwiseCorrect :: (1 <= w) => NatRepr w -> B.Domain w -> Integer -> Property
fromBitwiseCorrect w b x =
  B.proper w b ==> B.member b x ==>
    case fromBitwise w b of
      Nothing -> property True
      Just c -> property (member c (integerToNatural (x .&. maxUnsigned w)))

-- ------------------------------------------------------------------
-- ** Arithmetic

correct_neg :: (1 <= w) => NatRepr w -> Clp w -> Natural -> Property
correct_neg w c x =
  proper c ==> member c x ==>
    property (member (negate w c) (asN w (Prelude.negate (toInteger x))))

correct_add ::
  (1 <= w) =>
  NatRepr w -> Clp w -> Natural -> Clp w -> Natural -> Property
correct_add w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (add w a b) (asN w (toInteger x + toInteger y)))

correct_sub ::
  (1 <= w) =>
  NatRepr w -> Clp w -> Natural -> Clp w -> Natural -> Property
correct_sub w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (sub w a b) (asN w (toInteger x - toInteger y)))

correct_scale ::
  (1 <= w) =>
  NatRepr w -> Integer -> Clp w -> Natural -> Property
correct_scale w k c x =
  proper c ==> member c x ==>
    property (member (scale w k c) (asN w (k * toInteger x)))

correct_mul ::
  (1 <= w) =>
  NatRepr w -> Clp w -> Natural -> Clp w -> Natural -> Property
correct_mul w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (mul w a b) (asN w (toInteger x * toInteger y)))

correct_udiv ::
  (1 <= w) =>
  NatRepr w -> Clp w -> Natural -> Clp w -> Natural -> Property
correct_udiv w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> y /= 0 ==>
    property (member (udiv w a b) (x `quot` y))

correct_urem ::
  (1 <= w) =>
  NatRepr w -> Clp w -> Natural -> Clp w -> Natural -> Property
correct_urem w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> y /= 0 ==>
    property (member (urem w a b) (x `rem` y))

correct_sdiv ::
  (1 <= w) =>
  NatRepr w -> Clp w -> Natural -> Clp w -> Natural -> Property
correct_sdiv w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> ys /= 0 ==>
    property (member (sdiv w a b) (asN w (xs `quot` ys)))
  where
    xs = toSigned w (toInteger x)
    ys = toSigned w (toInteger y)

correct_srem ::
  (1 <= w) =>
  NatRepr w -> Clp w -> Natural -> Clp w -> Natural -> Property
correct_srem w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> ys /= 0 ==>
    property (member (srem w a b) (asN w (xs `rem` ys)))
  where
    xs = toSigned w (toInteger x)
    ys = toSigned w (toInteger y)

-- ------------------------------------------------------------------
-- *** Arithmetic (SMT-LIB div-by-zero semantics)

correct_udivSmtlib ::
  (1 <= w) =>
  NatRepr w -> Clp w -> Natural -> Clp w -> Natural -> Property
correct_udivSmtlib w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (udivSmtlib w a b) z)
  where
    z = if y == 0
          then fromInteger (maxUnsigned w)
          else x `quot` y

correct_uremSmtlib ::
  (1 <= w) =>
  NatRepr w -> Clp w -> Natural -> Clp w -> Natural -> Property
correct_uremSmtlib w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (uremSmtlib w a b) z)
  where
    z = if y == 0 then x else x `rem` y

correct_sdivSmtlib ::
  (1 <= w) =>
  NatRepr w -> Clp w -> Natural -> Clp w -> Natural -> Property
correct_sdivSmtlib w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (sdivSmtlib w a b) (asN w z))
  where
    xs = toSigned w (toInteger x)
    ys = toSigned w (toInteger y)
    z  = if ys == 0
           then if xs >= 0 then -1 else 1
           else xs `quot` ys

correct_sremSmtlib ::
  (1 <= w) =>
  NatRepr w -> Clp w -> Natural -> Clp w -> Natural -> Property
correct_sremSmtlib w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (sremSmtlib w a b) (asN w z))
  where
    xs = toSigned w (toInteger x)
    ys = toSigned w (toInteger y)
    z  = if ys == 0 then xs else xs `rem` ys

-- ------------------------------------------------------------------
-- ** Bitwise operations

correct_not :: (1 <= w) => NatRepr w -> Clp w -> Natural -> Property
correct_not w c x =
  proper c ==> member c x ==>
    property (member (not w c) (asN w (Bits.complement (toInteger x))))

correct_and ::
  (1 <= w) =>
  NatRepr w -> Clp w -> Natural -> Clp w -> Natural -> Property
correct_and w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (and w a b) (x Bits..&. y))

correct_or ::
  (1 <= w) =>
  NatRepr w -> Clp w -> Natural -> Clp w -> Natural -> Property
correct_or w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (or w a b) (x Bits..|. y))

correct_xor ::
  (1 <= w) =>
  NatRepr w -> Clp w -> Natural -> Clp w -> Natural -> Property
correct_xor w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (xor w a b) (Bits.xor x y))

-- ------------------------------------------------------------------
-- ** Concatenation, extension, selection, and truncation

correct_zero_ext ::
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Clp w -> NatRepr u -> Natural -> Property
correct_zero_ext w c u x =
  proper c ==> member c x ==> property (member (zext w c u) x)

correct_sign_ext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Clp w -> NatRepr u -> Natural -> Property
correct_sign_ext w c u x =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      proper c ==> member c x ==>
        property (member (sext w c u) (asN u (toSigned w (toInteger x))))

correct_concat ::
  forall u v.
  (1 <= u, 1 <= v) =>
  NatRepr u -> Clp u -> Natural ->
  NatRepr v -> Clp v -> Natural ->
  Property
correct_concat u a x v b y =
  case NR.leqAddPos u v of
    LeqProof ->
      let z = (x `Bits.shiftL` NR.widthVal v) Bits..|. y in
      proper a ==> proper b ==> member a x ==> member b y ==>
        property (member (concat u a v b) z)

correct_select ::
  forall i n w.
  (1 <= n, i + n <= w) =>
  NatRepr i -> NatRepr n -> NatRepr w -> Clp w -> Natural -> Property
correct_select i n w c x =
  case NR.leqTrans (LeqProof :: LeqProof 1 n)
                   (NR.leqTrans (NR.addPrefixIsLeq i n)
                                (LeqProof :: LeqProof (i + n) w)) of
    LeqProof ->
      let y = fromInteger ((toInteger x `Bits.shiftR` NR.widthVal i) Bits..&. maxUnsigned n) in
      proper c ==> member c x ==>
        property (member (select i n w c) y)

-- ------------------------------------------------------------------
-- ** Shifts and rotations

correct_shl ::
  (1 <= w) =>
  NatRepr w -> Clp w -> Natural -> Clp w -> Natural -> Property
correct_shl w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (shl w a b) z)
  where
    s = fromInteger (min (NR.intValue w) (toInteger y))
    z = asN w (toInteger x `Bits.shiftL` s)

correct_lshr ::
  (1 <= w) =>
  NatRepr w -> Clp w -> Natural -> Clp w -> Natural -> Property
correct_lshr w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (lshr w a b) z)
  where
    s = fromInteger (min (NR.intValue w) (toInteger y))
    z = fromInteger (toInteger x `Bits.shiftR` s)

correct_ashr ::
  (1 <= w) =>
  NatRepr w -> Clp w -> Natural -> Clp w -> Natural -> Property
correct_ashr w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (ashr w a b) z)
  where
    s = fromInteger (min (NR.intValue w) (toInteger y))
    z = asN w (toSigned w (toInteger x) `Bits.shiftR` s)

correct_rol ::
  (1 <= w) =>
  NatRepr w -> Clp w -> Natural -> Clp w -> Natural -> Property
correct_rol w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (rol w a b) (fromInteger (Arith.rotateLeft w (toInteger x) (toInteger y))))

correct_ror ::
  (1 <= w) =>
  NatRepr w -> Clp w -> Natural -> Clp w -> Natural -> Property
correct_ror w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (ror w a b) (fromInteger (Arith.rotateRight w (toInteger x) (toInteger y))))

-- ------------------------------------------------------------------
-- ** Helpers

-- | Reduce an 'Integer' modulo @2^w@ and return it as a 'Natural'.
asN :: NatRepr w -> Integer -> Natural
asN w x = fromInteger (x Bits..&. maxUnsigned w)

-- | Interpret the unsigned representation @x@ at width @w@ as a signed
-- 'Integer'.
toSigned :: (1 <= w) => NatRepr w -> Integer -> Integer
toSigned w x =
  if x' Bits..&. signBit == 0 then x' else x' - (signBit `Bits.shiftL` 1)
  where
    x' = x Bits..&. maxUnsigned w
    signBit = 1 `Bits.shiftL` (NR.widthVal w - 1)


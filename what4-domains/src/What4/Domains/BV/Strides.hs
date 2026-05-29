{-|
Module      : What4.Domains.BV.Strides
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Strides are an abstract domain for bitvectors. An element of the strides domain
is a tuple @(start, stride, n)@ representing the sequence of @n + 1@ bitvectors
visited by walking @n@ steps of size @stride@ from @start@ (mod @2^w@):

@
gamma((start, stride, n)) := { start + i * stride mod 2^w | 0 <= i <= n }
@

(Here, @gamma@ is the /concretization function/ in abstract interpretation.)

We call such a tuple a /progression/ in the sense of arithmetic progressions.

== /Intuition/

There are two "lossy" but helpful ways to conceptualize strided intervals.

=== /Geometry/

It can be helpful to conceptualize these progressions as strided intervals that
proceed clockwise around a \"number circle\". This circle starts at 0 at the
south pole, proceeds around to the signed maximum at the north pole (and then
immediately to the signed minimum), and ends at the unsigned maximum just before
0.

@
smax = 011..1 --vv-- 100..0 = smin
                --
              /    \
              \    /
                --
umin = 000..0 --^^-- 111..1 = umax
@

Unlike the classic interval domain over unbounded mathematical integers,
progressions can wrap around 0 from "high" values to "low" values (when
interpreted as unsigned bitvectors, i.e., with the lexicographical ordering on
their bits).

==== /Self-wrapping/

However, /and crucially/, this "geometric" intuition is limited. Unlike the
wrapped intervals domain (discussed further below), progressions can wrap around
/their own starting point/ without visiting the same value twice, even multiple
times. A progression with @gcd(stride, 2^w) = 1@ progression can visit every
element of @[0, 2^w - 1]@ before repeating. We call progressions that wrap in
this way /self-wrapping/.

=== /Algebra/

A progression @(start, stride, n)@ is a (not-necessarily-closed subset of a)
/coset/ @start + stride(ℤ/(2^w)ℤ)@ of the additive group ℤ/(2^w)ℤ.

== Visualization and examples

The diagrams below show the represented set as one cell per bitvector value
across @[0, 2^w)@; @*@ marks a member, @.@ a non-member. The outer brackets are
the modulus boundary - values fall off the right end and reappear on the left.

At @w = 4@:

@
[****************]   @top@ (the full set)
[..*****.........]   start=2,  stride=1, n=4: {2,3,4,5,6}
[..*.*.*.*.......]   start=2,  stride=2, n=3: {2,4,6,8}
[*...*...*...*...]   start=0,  stride=4, n=3: {0,4,8,12}
[**............**]   start=14, stride=1, n=3: {14,15,0,1}  (wraps around 0)
[*...........*.*.]   start=12, stride=2, n=2: {12,14,0}    (wraps around 0)
[*....*.*......*.]   start=0,  stride=7, n=3: {0,7,14,5}   (self-wrapping)
@

You can generate diagrams like the above with the following Python function:

@
def diagram(w, start, stride, n):
    members = {(start + i * stride) % (2 ** w) for i in range(n + 1)}
    cells = ''.join('*' if v in members else '.' for v in range(2 ** w))
    return f'[{cells}]'
@

which you can load into a REPL with

@
python3 -ic "$(awk '/^def diagram/,/^    return/' src/What4/Domains/BV/Strides.hs)"
@

== /Comparison to other domains/

The strides domain is similar to, but ultimately distinct from, a variety
of domains in the literature. The following are presented in ascending
chronological order of definition, but in roughly descending order of similarity
to the strides domain.

=== /Strided intervals/ (2006)

The strided interval (/SI/) domain of /Intermediate-Representation Recovery
from Low-Level Code/ is the reduced product of a finite-interval ([-2^(w-1),
2^(w-1)]) domain with a congruence domain. However, the SASI paper (see below)
states that "strided-intervals require the signedness of the variable and do not
take care of the value overflows and underflows." The strides domain takes great
pains to soundly handle over- and under-flows.

=== /Circular linear progressions/ (2007)

The strides domain is perhaps most similar to /circular linear progressions/
(CLPs), from /Executable Analysis using Abstract Interpretation with Circular
Linear Progressions/. A CLP is a tuple @(start, end, stride)@ representing the
set

@
gamma((start, end, stride)) :=
  { start + i * stride, start + 2 * i * stride, ..., end }
@

The immediate difference between CLPs and the strides domain is the
representation. We can easily recover @end@ from @(start, stride, n)@ in @O(w)@
via the identity @end = start + n * stride mod 2^w@, and check for self-wrap in
@O(w)@ via @n * stride >= 2^w@.

The procedure for deriving @n@ from @end@ is more complex. Let @g = gcd(2^w,
stride)@. Note that:

* @g@ is a power of 2,
* @stride / g@ is odd, and
* @stride / g@ and @2^w / g@ are coprime (by the definition of @gcd@).

Then @stride / g@ has a multiplicative inverse @s^(-1)@ mod @2^w / g@ that
can be computed via Hensel lifting (Newton iteration).  Subtracting @start@,
dividing by @g@, and multiplying by @s^(-1)@ on both sides yields @n@ as
desired:

@
((end - start) / g) * s^(-1) = n
@

Not only was this direction more complex, but also requires @O(w log w)@ time.
This is an important point of motivation for moving from CLP's @(start, end,
stride)@ to our @(start, stride, n)@.

An implementation of CLPs is available at
<https://github.com/statinf-otawa/otawa-clp>.

=== /Wrapped intervals/

In /Signedness-Agnostic Program Analysis: Precise Integer Bounds for Low-Level
Code/, the authors state that "Setting the stride in [CLPs] to 1 results in
precisely the concept of wrapped intervals that we use in this paper." Thus,
their /wrapped intervals/ (WIs) correspond closely to our stride-1 progressions.

Their wrapped intervals are pairs @(lo, hi)@ representing the set

@
gamma((lo, hi)) := { lo, lo + 1, ..., hi }
@

@lo@ does not need to be "less than" @hi@ in the sense of signed nor unsigned
bitvectors.

A self-wrapping stride-1 interval simply /saturates/ the space @[0, 2^w - 1]@.
Thus, the transfer functions (abstract operations) on WIs do not consider this
case. This is important, as they form the basis for the following domain.

=== /Signedness-agnostic strided intervals/

/Signedness-agnostic strided intervals/ (SASIs) (from the paper /BinTrimmer:
Towards Static Binary Debloating Through Abstract Interpretation/) are
based very closely on wrapped intervals, but they add stride information.
Fascinatingly, the /BinTrimmer/ paper does not cite the CLP paper, despite the
quote about CLPs in the /Signedness-Agnostic/ paper.

Like CLPs, SASIs are tuples @(lb, ub, s)@ representing the set

@
gamma((lb, ub, s)) := { lb, lb + s, lb + 2 * s ..., ub }
@

However, the membership check given in the paper is unsound with respect
to their @gamma@. It /is/ sound if we further assume that the SASIs don't
self-wrap. It's hard to say if the other operations on SASIs are sound with
respect to this non-self-wrapping interpretation, as the paper only specifies
@or@.

This unsoundness makes sense when we consider that SASIs are closely based on
WIs: self-wrapping does not matter for WIs (it saturates). The SASI operations
were not adequately adjusted for the new domain. The strides domain is what
results from adequately adjusting them.

Happily, this adjustment also improves precision. The implementation of addition
on SASIs at <https://github.com/ucsb-seclab/sasi> appears to saturate to top
when addition of the endpoints could overflow. However, this is not necessary
for strided intervals. Let @s@ be the SASI @(0, 2^n-2, 2)@. For @w=4@, we
can represent this visually as @[*.*.*.*.*.*.*.*.]@. Then pointwise addition
@gamma(s) + gamma(s) = { a + b | a in gamma(s), b in gamma(s) }@ yields exactly
@gamma(s) = {0, 2, ..., 2^(w-1)}@. That is to say, the most precise result
would be @s + s = s@, not top. This is what our 'add' yields on the equivalent
progressions.

== /Complexity/

This domain uses unbounded integers internally, and supports analysis of
variables of any bit-width @w@. Every exported operation is documented with its
complexity in big-O notation in terms of @w@. In particular, this means that
operations like bitwise-and on 'Natural' are considered @O(w)@.

== /Soundness/

A correctness (soundness) specification of every operation is given in
Cryptol in @doc\/clp.cry@; the Haskell @correct_*@ predicates here mirror that
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

module What4.Domains.BV.Strides
  ( Domain
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
  , hull
  , fromArith
  , toBitwise
  , fromBitwise
  -- * Queries
  , member
  , leq
  , leqPrecise
  , leqExact
  , toList
  , size
  -- , asSingleton
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
  , urem
  , sdiv
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
  -- * Lattice operations
  , meet
  , meetPrecise
  -- * Properties
  -- ** Generators
  , genDomain
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
  , floorSumCorrect
  , valueIndexCorrect
  , valueIndexMaybeCorrect
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
  , leqCorrect
  , leqReflexive
  , leqTransitive
  , leqRefinesLeqExact
  , leqPreciseCorrect
  , leqPreciseReflexive
  , leqPreciseRefinesLeqExact
  , leqExactCorrect
  , leqExactComplete
  , leqExactReflexive
  , leqExactTransitive
  , sizeViaToList
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
  , correct_urem
  , correct_sdiv
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
  -- ** Lattice operations
  , correct_meet
  , correct_meetPrecise
  , meetCommutative
  , meetPreciseCommutative
  , meetIdempotent
  , meetPreciseIdempotent
  , meetAssociative
  , meetPreciseAssociative
  , meetPreciseRefinesMeet
  , meetMonotone
  , meetPreciseMonotone
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

-- Note [Product abstraction]: A 'Domain' simultaneously over-approximates the
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
-- A progression is /self-wrapping/ when its conceptual arc revolves past its own
-- @start@ before reaching @end@: the cumulative distance walked
-- @n · stride@ exceeds @2^w@, where @n@ is the step count from @start@ to
-- @end@. Self-wrapping is strictly stronger than \"crosses the @0/2^w-1@
-- boundary\" — a progression can wrap around the number circle once without
-- self-wrapping (e.g. @{14, 0, 2}@ at width 4). See 'isSelfWrapping'.
--
-- For non-self-wrapping progressions the triple @(start, end, stride)@ encodes both
-- views at once: the arc walking @start → end@ by @stride@ visits exactly the
-- coset elements in their natural cyclic order. The two views are coupled
-- and mutually refining at no extra cost.
--
-- When the conceptual orbit self-wraps, the two views /decouple/: the orbit
-- visits a partial subset of a full coset, but @(s, e, t)@ cannot
-- disambiguate \"arc length @L@\" from \"arc length @L + 2^w/g · stride@\".
-- We must commit to a representable shape. The arithmetic ops have
-- closed-form step counts ('add', 'sub', 'mul'), saturating to the full
-- @g@-coset (via 'clampToOrbit') when the conceptual arc overruns its
-- representable length.

-- | A 'Domain' represents the set
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
data Domain (w :: Nat)
  = Domain
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
--   * /Self-wrapping is free/. A progression self-wraps when @n·stride ≥ 2^w@,
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
end :: Domain w -> Natural
end c@Domain{start, stride, n, mask} =
  assert (proper c) $ (start + n * stride) .&. mask
{-# INLINE end #-}

-- | The data-structure invariants of 'Domain'.
proper :: Domain w -> Bool
proper Domain {start, stride, n, mask} =
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

-- | /O(w)/. Reduce a 'Natural' modulo @2^w@, where @w@ is the width of the progression.
modMask :: Domain w -> Natural -> Natural
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
wrapOffset :: Domain w -> Natural -> Natural
wrapOffset c@Domain{start, mask} v =
  assert (proper c) $ modSub mask v start
{-# INLINE wrapOffset #-}

-- | /O(1)/. The lowest set bit of @x@; equivalently @gcd(x, 2^w)@ for any
-- @w@ at least the bit-length of @x@.
lowestSetBit :: Natural -> Natural
lowestSetBit x = 1 `shiftL` countTrailingZerosOr0 (toInteger x)
{-# INLINE lowestSetBit #-}

-- | /O(1)/. @gcd(stride, 2^w)@. Since @2^w@ is a power of two, this equals the
-- lowest set bit of @stride@.
strideGcd :: Domain w -> Natural
strideGcd Domain{stride} = lowestSetBit stride
{-# INLINE strideGcd #-}

-- | /O(w)/. @2^w \/ g@, where @mask = 2^w - 1@ and @g@ is a power-of-two
-- divisor of @2^w@ (e.g. @gcd(stride, 2^w)@). Used to compute the orbit
-- length of a progression from raw @mask@ and @g@ before a 'Domain' value exists.
orbitLenOf :: Natural -> Natural -> Natural
orbitLenOf mask g =
  assert (isPow2Natural (mask + 1)) $
  (mask + 1) `divByPow2` g
{-# INLINE orbitLenOf #-}

-- | /O(w)/. The orbit length: the number of distinct bitvectors visited by
-- the progression, which is @2^w \/ gcd(stride, 2^w)@. See
-- 'orbitLenViaToList'.
orbitLen :: Domain w -> Natural
orbitLen c@Domain{mask} = orbitLenOf mask (strideGcd c)
{-# INLINE orbitLen #-}

-- | /O(1)/. Cap @n@ at the orbit length minus 1: the maximum step count
-- representable for stride @stride@ at width @log2 (mask + 1)@.
clampToOrbit :: Natural -> Natural -> Natural -> Natural
clampToOrbit mask stride i =
  min i (orbitLenOf mask (lowestSetBit stride) - 1)
{-# INLINE clampToOrbit #-}

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

-- | /O(w^2)/. Euclidean-like floor sum,
-- @floorSum n m a b = sum_{i=0}^{n-1} ((a*i + b) \`Prelude.div\` m)@.
-- Requires @m > 0@; all values are non-negative.
floorSum :: Natural -> Natural -> Natural -> Natural -> Natural
floorSum n0 m0 a0 b0 = go 0 n0 m0 a0 b0
  where
    go !ans !n !m !a !b
      | n == 0 || m == 0 = ans
      | a >= m =
          go (ans + (n * (n - 1) `Prelude.div` 2) * (a `Prelude.div` m))
             n m (a `mod` m) b
      | b >= m =
          go (ans + n * (b `Prelude.div` m)) n m a (b `mod` m)
      | otherwise =
          let yMax = a * n + b
          in if yMax < m
               then ans
               else go ans (yMax `Prelude.div` m) a m (yMax `mod` m)

-- | /O(w log w)/. The progression index of @v@: the unique @i@ in @[0, 2^w \/
-- g)@ such that @start + i*stride ≡ v (mod 2^w)@, where @g = gcd(stride, 2^w)@.
-- Requires @g@ to divide @(v - start) mod 2^w@.
--
-- This costs O(w log w) for the modular inverse via 'invModPow2'; the step
-- count of the progression itself, @n c@, is available directly.
valueIndex :: Domain w -> Natural -> Natural
valueIndex c@Domain{stride, mask} v =
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

-- | /O(w log w)/. Like 'valueIndex', but returns 'Nothing' when @v@ is not on
-- the coset of @c@ (so 'valueIndex'\'s precondition would be violated).
valueIndexMaybe :: Domain w -> Natural -> Maybe Natural
valueIndexMaybe c v
  | wrapOffset c v `mod` strideGcd c == 0 = Just (valueIndex c v)
  | otherwise                             = Nothing
{-# INLINE valueIndexMaybe #-}

-- | /O(w)/. The value at progression index @i@: @(start + i * stride) mod 2^w@.
-- Left inverse of 'valueIndex' on indices in @[0, 2^w \/ g)@.
valueAt :: Domain w -> Natural -> Natural
valueAt c@Domain{start, stride} i = assert (proper c) $
  modMask c (start + i * stride)
{-# INLINE valueAt #-}

-- | /O(w)/. SASI and WI's @≤_x@: @a ≤_x b@ iff @(a - x) mod 2^w <= (b - x) mod
-- 2^w@. Equivalently, traversing the circle of bitvectors starting at @x@, @a@
-- is reached no later than @b@.
circLeq :: Natural -> Natural -> Natural -> Natural -> Bool
circLeq m x a b = (a + nx) .&. m <= (b + nx) .&. m
  where nx = modNeg m x

-- | /O(1)/. Does this progression self-wrap? A progression is self-wrapping if the
-- cumulative distance traversed by its orbit (@n * stride@, where @n@ is the
-- number of steps from @start@ to @end@) exceeds @2^w@. Geometrically: walking
-- around the number circle from @start@, the orbit passes its starting point
-- at least once before reaching @end@.
--
-- Note that all progressions are distinct by construction (any orbit of length
-- @≤ 2^w \/ gcd(stride, 2^w)@), so self-wrapping does /not/ mean residue
-- classes repeat. It only describes how far the orbit traveled.
isSelfWrapping :: Domain w -> Bool
isSelfWrapping Domain{stride, n, mask} = n * stride > mask
{-# INLINE isSelfWrapping #-}

-- ------------------------------------------------------------------
-- * Construction

-- | Construct a progression from @(start, stride, n)@: the orbit
-- @{ start, start + stride, ..., start + n·stride }@ (all mod @2^w@).
-- Asserts that @start@ and @stride@ fit in @w@ bits, that @stride > 0@, that
-- @n@ is within the orbit length @2^w \/ gcd(stride, 2^w)@, and that the
-- resulting element is 'proper'.
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
  Domain w
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
    c = Domain { start = s', stride = st', n = n', mask = m }
{-# INLINE mk #-}

-- ------------------------------------------------------------------
-- * Conversion

-- | /O(w)/. Convert a progression to an arithmetic domain (wrapped interval).
--
-- For non-self-wrapping progressions, the result is the interval @[start, end]@
-- (over-approximating by collapsing to stride = 1). For self-wrapping progressions,
-- the orbit visits exactly the values congruent to @start@ modulo
-- @g = gcd(stride, 2^w)@, so we use the tightest such interval:
-- @[start \`mod\` g, mask + 1 - g + (start \`mod\` g)]@.
toArith :: Domain w -> A.Domain w
-- For self-wrapping progressions, this does not yield the tightest interval
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
startEndArc :: Domain w -> A.Domain w
startEndArc c@Domain{start = s, stride = t, n = nn, mask = m} =
  assert (proper c) $
  assert (Prelude.not (isSelfWrapping c)) $
  -- Non-self-wrapping: @n·stride < 2^w@, so the arc length is exactly @n·t@.
  A.interval (toInteger m) (toInteger s) (toInteger (nn * t))

-- | /O(w)/. The arc @[start \`mod\` g, ..., start \`mod\` g + (2^w - g)]@,
-- where @g = gcd(stride, 2^w)@. The union of all bitvectors congruent to
-- @start@ modulo @g@; sound on any progression, but only a tight cover on
-- self-wrapping orbits, so caller must ensure the input is self-wrapping.
cosetArc :: Domain w -> A.Domain w
cosetArc c@Domain{start = s, mask = m} =
  assert (proper c) $
  assert (isSelfWrapping c) $
  let g = strideGcd c
      imask = toInteger m
      lo = toInteger (s .&. (g - 1))
  in A.interval imask lo (imask + 1 - toInteger g)

-- | /O(w)/. Convert an arithmetic domain (wrapped interval) to a progression.
fromArith :: NatRepr w -> A.Domain w -> Maybe (Domain w)
fromArith w = \case
  A.BVDAny _mask -> Just (mk w 0 1 (integerToNatural imask))
    where imask = maxUnsigned w
  d | A.isBottom d -> Nothing
    | otherwise -> case A.arithDomainData d of
        Nothing -> Nothing
        Just (lo, sz) -> Just (mk w (integerToNatural lo) 1 (integerToNatural sz))

-- TODO: The arith<->bitwise helpers below duplicate
-- 'arithToBitwiseDomain'/'bitwiseToArithDomain' in "What4.Domains.BV". Once
-- those are moved into a common module that 'Strides' can import (e.g. by adding a
-- dep from 'BV.Bitwise' to 'BV.Arith'), inline-call them instead.

-- TODO? Can we do better than just arith-to-bitwise by considering stride?

-- | /O(w log w)/. Convert a progression to a bitwise domain.
toBitwise :: Domain w -> B.Domain w
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

-- | /O(1)/. Convert a bitwise domain to a progression.
fromBitwise :: NatRepr w -> B.Domain w -> Maybe (Domain w)
fromBitwise w b = fromArith w (bitwiseToArith b)
  where
    bitwiseToArith d =
      let imask = B.bvdMask d
          (lo, hi) = B.bitbounds d
      in A.interval imask lo ((hi - lo) Bits..&. imask)

-- ------------------------------------------------------------------
-- * Queries

-- | /O(w log w)/. Test if the given value is a member of the progression.
member :: Domain w -> Natural -> Bool
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
  case valueIndexMaybe c v of
    Just i  -> i <= n c
    Nothing -> False

-- | /O(w)/. Sound, reflexive, and transitive (and so cheap to compose) but
-- coarse approximation of 'leqExact'. Use 'leqPrecise' for a finer (but
-- non-transitive) check, or 'leqExact' for an exact (but quadratic) one.
leq :: Domain w -> Domain w -> Bool
-- Writing @stride = 2^v · m@ for odd @m@, the subgroup @⟨stride⟩@ in
-- @Z\/2^w@ is @⟨2^v⟩@. We accept @a ⊆ b@ if /any/ of:
--
--   (1) /Equal/: @a == b@. Transitive on the nose.
--   (2) /Singleton/: @a@ is a single element and lies in @b@. Composes
--       with the others by membership transitivity.
--   (3) /Full b/, in three parts:
--         (3a) @b@ spans its full orbit (@n b + 1 == orbitLen b@);
--         (3b) /Coset/: @start a − start b ∈ ⟨stride b⟩@; and
--         (3c) /Subgroup/: @⟨stride a⟩ ⊆ ⟨stride b⟩@, i.e. @strideGcd b@
--              divides @stride a@.
--       If both @b@ and @c@ are full, the coset and subgroup containments
--       chain: @⟨stride a⟩ ⊆ ⟨stride b⟩ ⊆ ⟨stride c⟩@, etc.
leq a b = assert (proper a) $ assert (proper b) $
  equal               -- (1)
  || singletonInB     -- (2)
  || (bIsFull         -- (3a)
        && cosetMatches      -- (3b)
        && subgroupContained -- (3c)
     )
  where
    equal             = a == b
    singletonInB      = n a == 0 && member b (start a)
    bIsFull           = n b + 1 == orbitLen b
    cosetMatches      = wrapOffset b (start a) `mod` strideGcd b == 0
    subgroupContained = stride a `mod` strideGcd b == 0

-- | /O(w log w)/. Sound and finer approximation of 'leqExact' than 'leq'.
-- Reflexive but, as a syntactic approximation, not transitive in general.
leqPrecise :: Domain w -> Domain w -> Bool
-- The check embeds @a@\'s orbit into @b@\'s index space:
--
--   (1) /On orbit/: @start a@ lies on @b@\'s orbit (at some @b@-index
--       @iAStart@), and @iAStart <= n b@.
--   (2) /Singleton/: if @a@ is a singleton, (1) is enough.
--   (3) Otherwise:
--         (3a) /Stride aligned/: @stride b@ divides @stride a@; that
--              multiple @aStepInB@ is how far each step of @a@ advances
--              in @b@-index space; and
--         (3b) /Fits in b/: after @n a@ such steps, the @b@-index reached
--              still does not exceed @n b@.
leqPrecise a b = assert (proper a) $ assert (proper b) $
  case valueIndexMaybe b (start a) of
    Nothing      -> False  -- (1) start a not on b's orbit
    Just iAStart ->
      onOrbit iAStart                       -- (1)
      && (aIsSingleton                      -- (2)
          || (strideAligned                 -- (3a)
              && aFitsInsideB iAStart       -- (3b)
             ))
  where
    aIsSingleton  = n a == 0
    onOrbit i     = i <= n b
    strideAligned = stride a `mod` stride b == 0
    aStepInB      = stride a `Prelude.div` stride b
    aFitsInsideB i = i + n a * aStepInB <= n b

-- | /O(w^2)/. Partial order on progressions: @leqExact a b@ iff every element
-- of @a@ is in @b@.
leqExact :: Domain w -> Domain w -> Bool
-- Writing @stride = 2^v · m@ for odd @m@, the subgroup of @Z\/2^w@ generated
-- by @stride@ is @⟨2^v⟩@ — the odd factor @m@ is invertible mod @2^w\/2^v@
-- and so doesn\'t change which subgroup is generated. The check is then:
--
--   (1) /Coset/: @start a@ lies on @b@\'s coset, i.e. @start a − start b ∈
--       ⟨2^{v_b}⟩@. Read off as @b@-index @iAStart@.
--   (2) /Subgroup/: @⟨stride a⟩ ⊆ ⟨stride b⟩@, i.e. @v_a ≥ v_b@. Equivalent
--       to @2^{v_b} = strideGcd b@ dividing @stride a@.
--   (3) /Window/: the indices @{ iAStart + i · aStep mod orbitLen b
--       | 0 ≤ i ≤ n a }@ all lie in @[0, n b]@, where
--       @aStep = stride a · stride b^{-1} mod orbitLen b@ in @b@\'s index space.
--
-- The window count uses 'floorSum' to compute, in @O(w log w)@, how many of
-- the @n a + 1@ visited indices fall in @[0, n b]@.
leqExact a b = assert (proper a) $ assert (proper b) $
  case valueIndexMaybe b (start a) of
    Nothing -> False                             -- (1) fails: start a off coset
    Just iAStart
      | aIsSingleton          -> iAStart <= n b  -- (1) ok; (2)/(3) vacuous
      | Prelude.not subgroupContained -> False   -- (2) fails
      | bIsFull               -> True            -- (3) vacuous: full orbit
      | otherwise             -> windowFits iAStart  -- (3)
  where
    gB :: Natural
    gB = strideGcd b
    mB :: Natural
    mB = orbitLen b
    aIsSingleton, subgroupContained, bIsFull :: Bool
    aIsSingleton      = n a == 0
    subgroupContained = stride a `mod` gB == 0   -- (2)
    bIsFull           = n b + 1 == mB
    -- @a@'s stride translated to @b@-index space, modulo b's orbit length.
    invSB, aStep :: Natural
    invSB = invModPow2 (stride b `divByPow2` gB) mB
    aStep = ((stride a `divByPow2` gB) * invSB) .&. (mB - 1)
    -- (3): of the @n a + 1@ visited @b@-indices, count how many fall in
    -- @[0, n b]@; the AP fits iff that count is @n a + 1@.
    windowFits :: Natural -> Bool
    windowFits iAStart =
      let nA1     = n a + 1
          wWidth  = n b + 1
          hits    = nA1 + floorSum nA1 mB aStep iAStart
                        - floorSum nA1 mB aStep (iAStart + mB - wWidth)
      in hits == nA1

-- | /O(2^w \/ g)/, where @g = gcd(stride, 2^w)@. Enumerate the (distinct)
-- elements of a progression, in the order they are produced by the progression:
-- @start, start + stride, ..., end@ (all mod @2^w@).
toList :: Domain w -> [Natural]
-- References:
--
-- * CLP Section 3, @conc@
-- * SASI Definition 1, Concretization function
toList c@Domain{start, stride, n} = assert (proper c) $ go 0 start
  where
    go !i !v
      | i == n    = [v]
      | otherwise = v : go (i + 1) (modMask c (v + stride))

-- | /O(1)/. The number of distinct values in the progression: @n + 1@.
size :: Domain w -> Natural
size c@Domain{n} = assert (proper c) $ n + 1
{-# INLINE size #-}

-- ------------------------------------------------------------------
-- * Lifted operations

-- These helpers convert a progression to an arithmetic or bitwise domain, apply the
-- corresponding operation there, and convert back. Since the result of an
-- @A.*@ or @B.*@ op on a proper input is always proper (never bottom),
-- @fromArith@\/@fromBitwise@ here always succeed, and we project from the
-- 'Maybe' with 'fromJustUnsafe'. This loses precision (the round-trip
-- collapses non-trivial strides), but is sound.

fromJustUnsafe :: String -> Maybe a -> a
fromJustUnsafe loc = \case
  Just x  -> x
  Nothing -> error ("What4.Domains.BV.Strides: " ++ loc ++ ": Nothing")
{-# INLINE fromJustUnsafe #-}

liftArith1 ::
  (1 <= w) =>
  NatRepr w ->
  (A.Domain w -> A.Domain w) ->
  Domain w -> Domain w
liftArith1 w f c =
  fromJustUnsafe "liftArith1" (fromArith w (f (toArith c)))
{-# INLINE liftArith1 #-}

liftArith2 ::
  (1 <= w) =>
  NatRepr w ->
  (A.Domain w -> A.Domain w -> A.Domain w) ->
  Domain w -> Domain w -> Domain w
liftArith2 w f a b =
  fromJustUnsafe "liftArith2" (fromArith w (f (toArith a) (toArith b)))
{-# INLINE liftArith2 #-}

liftBitwise1 ::
  (1 <= w) =>
  NatRepr w ->
  (B.Domain w -> B.Domain w) ->
  Domain w -> Domain w
liftBitwise1 w f c =
  fromJustUnsafe "liftBitwise1" (fromBitwise w (f (toBitwise c)))
{-# INLINE liftBitwise1 #-}

liftBitwise2 ::
  (1 <= w) =>
  NatRepr w ->
  (B.Domain w -> B.Domain w -> B.Domain w) ->
  Domain w -> Domain w -> Domain w
liftBitwise2 w f a b =
  fromJustUnsafe "liftBitwise2" (fromBitwise w (f (toBitwise a) (toBitwise b)))
{-# INLINE liftBitwise2 #-}

-- ------------------------------------------------------------------
-- * Arithmetic

-- | /O(w)/. Negation: stride is preserved; the orbit reverses, so the new
-- @start@ is the old @end@ negated. The step count @n@ is unchanged.
negate :: (1 <= w) => NatRepr w -> Domain w -> Domain w
negate w c@Domain{stride, n = nn, mask} =
  assert (proper c) $
  mk w (modNeg mask (end c)) stride nn

-- | /O(w)/. Addition.
add :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
-- References:
--
-- * CLP 4.2 Arithmetic Operations
-- * WI 3.2 Analysing expressions
--
-- In the CLP (start, end, stride) formulation, they give:
--
--   (l1, u1, δ1) + (l2, u2, δ2) := (l1 + l2, u1 + u2, gcd(δ1, δ2))
--
-- (This only works with some assumptions on endpoint ordering and overflow.)
--
-- Shift each orbit by the other's @start@, then walk @span\'@ steps from
-- @start a + start b@ in stride @d = gcd(stride a, stride b)@ (with singleton
-- operands skipped), where @span' = n a · (stride a / d) + n b · (stride b / d)@
-- — both ratios are exact since @d@ divides both strides. The conceptual
-- orbit may overshoot the available step count (e.g. when summing two full
-- cosets @span'@ doubles); 'clampToOrbit' caps it, and 'mk' canonicalizes
-- the saturated case to the full coset of @start'@.
add w a b =
  assert (proper a) $
  assert (proper b) $
  mk w start' d (clampToOrbit (mask a) d n')
  where
    d = strideGcd2 a b
    n' = n a * (stride a `div` d) + n b * (stride b `div` d)
    start' = modMask a (start a + start b)

-- | /O(w)/. Subtraction.
sub :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sub w a b =
  assert (proper a) $
  assert (proper b) $
  mk w start' d (clampToOrbit (mask a) d n')
  where
    d = strideGcd2 a b
    n' = n a * (stride a `div` d) + n b * (stride b `div` d)
    start' = modSub (mask a) (start a) (end b)

-- | Result stride for 'add'\/'sub': @gcd(stride a, stride b)@, with singleton
-- operands skipped (their stride is the dummy value @1@, which would otherwise
-- collapse the result stride).
strideGcd2 :: Domain w -> Domain w -> Natural
strideGcd2 a b = case (n a, n b) of
  (0, 0) -> 1
  (0, _) -> stride b
  (_, 0) -> stride a
  _      -> Prelude.gcd (stride a) (stride b)

-- | The progression whose elements are exactly those of @arith@ that lie in the
-- @g@-coset of @start'@, where @g = lowestSetBit d@. Strictly tighter than
-- the corresponding @liftArith*@ call when @g > 1@, since the stride stays
-- @g@ rather than collapsing to 1. See Note [Product abstraction].
--
-- Currently unused; retained as a building block for an Arith-Strides reduced
-- product.
_arithMeetCoset ::
  (1 <= w) =>
  NatRepr w ->
  -- | The Arith arc to restrict.
  A.Domain w ->
  -- | Result stride @d@: must be positive and at most @2^w - 1@.
  Natural ->
  -- | @start'@: any representative of the target coset.
  Natural ->
  Domain w
_arithMeetCoset w arith d start' =
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

scale :: (1 <= w) => NatRepr w -> Integer -> Domain w -> Domain w
scale w k = liftArith1 w (A.scale k)

-- | The effective @(lo, stride)@ pair used by 'mul' for the result-stride
-- formula. Singletons contribute stride 0 (their orbit has no nontrivial
-- differences).
effLoStride :: Domain w -> (Natural, Natural)
effLoStride c
  | n c == 0  = (start c, 0)
  | otherwise = (start c, stride c)

-- | /O(w)/. Multiplication.
mul :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
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
-- (This only works with some assumptions on endpoint ordering and overflow.)
--
-- Note that WI 3.2 Analysing expressions has a significantly more complex
-- definition of multiplication that splits the intervals at the poles, does
-- piecewise signed/unsigned multiplication, and joins the results. This may be
-- more precise, and we might want to implement it in the future.
--
-- Expanding @(l1 + i·t1)(l2 + j·t2)@ for @0 ≤ i ≤ n a@, @0 ≤ j ≤ n b@ gives
--
-- @
-- start' + i·(t1·l2) + j·(t2·l1) + i·j·(t1·t2)   (mod 2^w)
-- @
--
-- where @start' = l1·l2 mod 2^w@. So the products land in the coset of
-- @start'@ modulo @d = gcd(t1·l2, t2·l1, t1·t2)@: those are the three step
-- sizes from holding one factor fixed and stepping the other (the @t1·t2@
-- term is the cross when both step). The maximum non-modular displacement is
-- @n a·(t1·l2) + n b·(t2·l1) + n a·n b·(t1·t2)@; dividing by @d@ gives a
-- step-count bound, which 'clampToOrbit' caps at the orbit length when the
-- conceptual progression overruns its full coset.
mul w a b =
  assert (proper a) $
  assert (proper b) $
  if dMod == 0
    then mk w start' 1 0
    else mk w start' dMod (clampToOrbit (mask a) dMod n')
  where
    (l1, t1) = effLoStride a
    (l2, t2) = effLoStride b
    d12    = t1 * l2
    d21    = t2 * l1
    d22    = t1 * t2
    dInt   = Prelude.gcd d12 (Prelude.gcd d21 d22)
    dMod   = modMask a dInt
    n'     = n a * (d12 `div` dInt)
           + n b * (d21 `div` dInt)
           + n a * n b * (d22 `div` dInt)
    start' = modMask a (start a * start b)

udiv :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
udiv w = liftArith2 w A.udiv

urem :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
urem w = liftArith2 w A.urem

sdiv :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sdiv w = liftArith2 w (A.sdiv w)

srem :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
srem w = liftArith2 w (A.srem w)

-- ------------------------------------------------------------------
-- ** Arithmetic (SMT-LIB div-by-zero semantics)

udivSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
udivSmtlib w = liftArith2 w A.udivSmtlib

uremSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
uremSmtlib w = liftArith2 w A.uremSmtlib

sdivSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sdivSmtlib w = liftArith2 w (A.sdivSmtlib w)

sremSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sremSmtlib w = liftArith2 w (A.sremSmtlib w)

-- ------------------------------------------------------------------
-- * Bitwise operations

not :: (1 <= w) => NatRepr w -> Domain w -> Domain w
not w = liftBitwise1 w B.not

and :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
and w = liftBitwise2 w B.and

or :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
or w = liftBitwise2 w B.or

xor :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
xor w = liftBitwise2 w B.xor

-- ------------------------------------------------------------------
-- * Concatenation, extension, selection, and truncation

zext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Domain u
zext _w c u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      fromJustUnsafe "zext" (fromArith u (A.zext (toArith c) u))

sext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Domain u
sext w c u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      fromJustUnsafe "sext" (fromArith u (A.sext w (toArith c) u))

concat ::
  forall u v.
  (1 <= u, 1 <= v) =>
  NatRepr u -> Domain u -> NatRepr v -> Domain v -> Domain (u + v)
concat u a v b =
  case NR.leqAddPos u v of
    LeqProof ->
      fromJustUnsafe "concat"
        (fromArith (NR.addNat u v) (A.concat u (toArith a) v (toArith b)))

select ::
  forall i n w.
  (1 <= n, 1 <= w, i + n <= w) =>
  NatRepr i -> NatRepr n -> NatRepr w -> Domain w -> Domain n
select i n _w c =
  fromJustUnsafe "select" (fromArith n (A.select i n (toArith c)))

-- ------------------------------------------------------------------
-- * Shifts and rotations

shl :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
shl w = liftArith2 w (A.shl w)

lshr :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
lshr w = liftArith2 w (A.lshr w)

ashr :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
ashr w = liftArith2 w (A.ashr w)

rol :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
rol w = liftBitwise2 w (B.rolAbstract w)

ror :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
ror w = liftBitwise2 w (B.rorAbstract w)

-- ------------------------------------------------------------------
-- * Lattice operations

-- | /O(w)/. Lattice meet: a sound /over/-approximation of the
-- intersection of two progressions. For any concrete value @x@, if @x@
-- is a member of both @a@ and @b@, then @x@ is a member of @meet a b@.
-- Returns 'Nothing' when the result would be empty.
--
-- Uses 'leq' (the cheap reflexive+transitive variant) for the containment
-- short-circuits. See 'meetPrecise' for the variant that uses 'leqExact'
-- short-circuits.
--
-- Not currently a lower bound (TODO).
meet ::
  (1 <= w) =>
  NatRepr w ->
  Domain w -> Domain w -> Maybe (Domain w)
meet w a b =
  assert (proper a) $
  assert (proper b) $
  case () of
    _ | leq a b -> Just a
      | leq b a -> Just b
      | otherwise -> meetStrides w a b

-- | /O(w^2)/. Like 'meet', but uses 'leqExact' for the containment
-- short-circuits — preserves the smaller operand exactly when one is
-- contained in the other (whereas 'meet' may miss some containment
-- cases that 'leq' is too coarse to detect, and fall through to
-- 'meetStrides' which collapses to the gcd-of-cosets stride).
meetPrecise ::
  (1 <= w) =>
  NatRepr w ->
  Domain w -> Domain w -> Maybe (Domain w)
meetPrecise w a b =
  assert (proper a) $
  assert (proper b) $
  case () of
    _ | leqExact a b -> Just a
      | leqExact b a -> Just b
      | otherwise -> meetStrides w a b

-- | /O(w)/. Sound (over-approximating) intersection of two progressions, used
-- as the general (non-short-circuit) path of 'meet' and 'meetPrecise'.
--
-- The arc constraint is handled by 'A.meet' on the 'hull's
-- @[start, start + n·stride]@ of each operand (saturating to top on
-- self-wrap); 'fromArith' then converts the resulting arc back to a
-- stride-1 progression. Using 'hull' (rather than 'toArith', which
-- falls back to 'cosetArc' on self-wrapping orbits) keeps the result
-- a refinement of both inputs' arcs. The coset compatibility check
-- guards against the case where the two operand cosets are disjoint
-- (in which case the result is empty regardless of the arc overlap).
meetStrides ::
  (1 <= w) =>
  NatRepr w ->
  Domain w -> Domain w -> Maybe (Domain w)
meetStrides w a b =
  let g_a = strideGcd a
      g_b = strideGcd b
      delta = modSub (mask a) (start a) (start b)
  in if delta .&. (min g_a g_b - 1) /= 0
       then Nothing
       else fromArith w (A.meet (hull a) (hull b))

-- | The arith hull of a progression: the arc @[start, start + n·stride]@.
-- Saturates to top when @n·stride >= 2^w@ (i.e., on self-wrapping orbits).
-- Differs from 'toArith', which falls back to 'cosetArc' for self-wrap.
hull :: Domain w -> A.Domain w
hull c@Domain{start = s, stride = t, n = nn, mask = m} =
  assert (proper c) $
  A.interval (toInteger m) (toInteger s) (toInteger (nn * t))

-- ------------------------------------------------------------------
-- * Generators

-- | Generator for a proper 'Domain' at width @w@.
genDomain :: NatRepr w -> Gen (Domain w)
genDomain w = do
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

-- | Generate a random element of the given (proper) progression.
genElement :: Domain w -> Gen Natural
genElement c = do
  i <- integerToNatural <$> chooseInteger (0, toInteger (n c))
  pure (valueAt c i)

-- | Generate a random progression and an element contained in it.
genPair :: NatRepr w -> Gen (Domain w, Natural)
genPair w = do
  c <- genDomain w
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
wrapOffsetCorrect :: Domain w -> Natural -> Property
wrapOffsetCorrect c v =
  proper c ==>
    property (modMask c (start c + wrapOffset c v) == modMask c v)

-- | @strideGcd c@ divides @stride c@ and divides @2^w@.
strideGcdDividesStride :: Domain w -> Property
strideGcdDividesStride c =
  proper c ==>
    property (stride c `mod` strideGcd c == 0
           && (mask c + 1) `mod` strideGcd c == 0)

-- | @strideGcd c@ is a power of two (i.e. @g .&. (g - 1) == 0@).
strideGcdIsPow2 :: Domain w -> Property
strideGcdIsPow2 c =
  proper c ==> property (g > 0 && g .&. (g - 1) == 0)
  where g = strideGcd c

-- | 'orbitLen' upper-bounds the length of 'toList': it equals the number of
-- distinct values reachable from @start@ by stepping by @stride@, while
-- 'toList' stops early at @end@.
orbitLenViaToList :: Domain w -> Property
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

-- | 'floorSum' agrees with the naive sum:
-- @floorSum n m a b == sum_{i=0}^{n-1} ((a*i + b) \`Prelude.div\` m)@.
-- @n@, @a@, @b@ are clamped to small ranges to keep the naive sum cheap.
floorSumCorrect :: Natural -> Natural -> Natural -> Natural -> Property
floorSumCorrect n m a b =
  m' > 0 ==>
    property (floorSum n' m' a' b' == naive)
  where
    n' = n `mod` 64
    m' = (m `mod` 32) + 1
    a' = a `mod` 64
    b' = b `mod` 64
    naive = sum [ (a' * i + b') `Prelude.div` m'
                | n' > 0, i <- [0 .. n' - 1] ]

-- | @valueAt c (valueIndex c v) ≡ v (mod 2^w)@ whenever @v@ is on the
-- progression (i.e. @strideGcd c@ divides @wrapOffset c v@).
valueIndexCorrect :: Domain w -> Natural -> Property
valueIndexCorrect c v =
  proper c ==> wrapOffset c v' `mod` strideGcd c == 0 ==>
    property (valueAt c (valueIndex c v') == v')
  where v' = modMask c v

-- | 'valueIndexMaybe' returns 'Just' iff @v@ is on @c@\'s coset, and the
-- payload agrees with 'valueIndex'.
valueIndexMaybeCorrect :: Domain w -> Natural -> Property
valueIndexMaybeCorrect c v =
  proper c ==>
    let v' = modMask c v
        onCoset = wrapOffset c v' `mod` strideGcd c == 0
    in property $ case valueIndexMaybe c v' of
         Just i  -> onCoset && i == valueIndex c v'
         Nothing -> Prelude.not onCoset

-- | @valueIndex c (valueAt c i) == i@ for any @i@ in @[0, orbitLen c)@.
valueAtCorrect :: Domain w -> Natural -> Property
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

-- | 'isSelfWrapping' agrees with the orbit length: a progression is self-wrapping iff
-- stepping through every element of 'toList' travels strictly more than @2^w@
-- in total. Concretely, @isSelfWrapping c@ iff
-- @(length (toList c) - 1) * stride > 2^w - 1@.
isSelfWrappingViaToList :: Domain w -> Property
isSelfWrappingViaToList c@Domain{stride, mask} =
  proper c ==> property (isSelfWrapping c == (k * stride > mask))
  where
    k = fromIntegral (length (toList c) - 1) :: Natural

-- ------------------------------------------------------------------
-- ** Queries

-- | A progression always contains its own @start@.
startMember :: Domain w -> Property
startMember c = proper c ==> property (member c (start c))

-- | A progression always contains its own @end@.
endMember :: Domain w -> Property
endMember c = proper c ==> property (member c (end c))

-- | Every element produced by 'toList' is a member of the progression.
toListMember :: Domain w -> Property
toListMember c =
  proper c ==> property (Prelude.all (member c) (toList c))

-- | If 'member' returns 'True' for some bitvector @x@, then @x@ appears in
-- 'toList'.
memberToList :: Domain w -> Natural -> Property
memberToList c x =
  proper c ==> (member c x' ==> property (x' `elem` toList c))
  where x' = modMask c x

-- | 'toList' produces no duplicate elements.
toListNoDuplicates :: Domain w -> Property
toListNoDuplicates c = proper c ==> property (noDuplicates (toList c))
  where
    noDuplicates xs = length xs == Set.size (Set.fromList xs)

-- | Soundness of 'leq': if @a \`leq\` b@ then every element of @a@ is in @b@.
leqCorrect :: Domain w -> Domain w -> Property
leqCorrect a b =
  proper a ==> proper b ==> mask a == mask b ==>
    leq a b ==> property (Prelude.all (member b) (toList a))

-- | 'leq' is reflexive.
leqReflexive :: Domain w -> Property
leqReflexive a = proper a ==> property (leq a a)

-- | 'leq' is transitive: if @a \`leq\` b@ and @b \`leq\` c@ then
-- @a \`leq\` c@. (Both 'leqPrecise' and 'leqExact' are reflexive but not
-- guaranteed transitive at the syntactic level; only 'leq' is.)
leqTransitive :: Domain w -> Domain w -> Domain w -> Property
leqTransitive a b c =
  proper a ==> proper b ==> proper c ==>
    mask a == mask b ==> mask b == mask c ==>
      leq a b ==> leq b c ==> property (leq a c)

-- | 'leq' refines 'leqExact': @leq a b ==> leqExact a b@. ('leq' and
-- 'leqPrecise' are not comparable in general — neither refines the other.)
leqRefinesLeqExact :: Domain w -> Domain w -> Property
leqRefinesLeqExact a b =
  proper a ==> proper b ==> mask a == mask b ==>
    leq a b ==> property (leqExact a b)

-- | Soundness of 'leqPrecise': if @a \`leqPrecise\` b@ then every element
-- of @a@ is in @b@.
leqPreciseCorrect :: Domain w -> Domain w -> Property
leqPreciseCorrect a b =
  proper a ==> proper b ==> mask a == mask b ==>
    leqPrecise a b ==> property (Prelude.all (member b) (toList a))

-- | 'leqPrecise' is reflexive.
leqPreciseReflexive :: Domain w -> Property
leqPreciseReflexive a = proper a ==> property (leqPrecise a a)

-- | 'leqPrecise' refines 'leqExact': @leqPrecise a b ==> leqExact a b@.
-- Equivalently, 'leqPrecise' is a sound approximation of the semantic
-- containment that 'leqExact' decides.
leqPreciseRefinesLeqExact :: Domain w -> Domain w -> Property
leqPreciseRefinesLeqExact a b =
  proper a ==> proper b ==> mask a == mask b ==>
    leqPrecise a b ==> property (leqExact a b)

-- | Soundness of 'leqExact': @leqExact a b@ implies every element of @a@ is
-- in @b@.
leqExactCorrect :: Domain w -> Domain w -> Property
leqExactCorrect a b =
  proper a ==> proper b ==> mask a == mask b ==>
    leqExact a b ==> property (Prelude.all (member b) (toList a))

-- | Completeness of 'leqExact': if every element of @a@ is in @b@, then
-- @leqExact a b@. Together with 'leqExactCorrect' this says @leqExact@
-- decides semantic containment exactly.
leqExactComplete :: Domain w -> Domain w -> Property
leqExactComplete a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.all (member b) (toList a) ==> property (leqExact a b)

-- | 'leqExact' is reflexive.
leqExactReflexive :: Domain w -> Property
leqExactReflexive a = proper a ==> property (leqExact a a)

-- | 'leqExact' is transitive: if @a \`leqExact\` b@ and @b \`leqExact\` c@
-- then @a \`leqExact\` c@.
leqExactTransitive :: Domain w -> Domain w -> Domain w -> Property
leqExactTransitive a b c =
  proper a ==> proper b ==> proper c ==>
    mask a == mask b ==> mask b == mask c ==>
      leqExact a b ==> leqExact b c ==> property (leqExact a c)

-- | 'size' agrees with the length of 'toList'.
sizeViaToList :: Domain w -> Property
sizeViaToList c =
  proper c ==> property (size c == fromIntegral (length (toList c)))

-- ------------------------------------------------------------------
-- ** Conversion

-- | Every element in a progression is also in its 'toArith' conversion.
toArithCorrect :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
toArithCorrect _w c x =
  proper c ==> member c x' ==>
    property (A.member (toArith c) (toInteger x'))
  where
    x' = modMask c x

-- | On non-self-wrapping progressions, every orbit member lies in 'startEndArc'.
startEndArcCorrect :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
startEndArcCorrect _w c x =
  proper c ==> Prelude.not (isSelfWrapping c) ==> member c x' ==>
    property (A.member (startEndArc c) (toInteger x'))
  where
    x' = modMask c x

-- | On self-wrapping progressions, every orbit member lies in 'cosetArc'.
cosetArcCorrect :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
cosetArcCorrect _w c x =
  proper c ==> isSelfWrapping c ==> member c x' ==>
    property (A.member (cosetArc c) (toInteger x'))
  where
    x' = modMask c x

-- | Every element in an arithmetic domain is also in its 'fromArith' conversion
-- (when that conversion produces a progression).
fromArithCorrect :: (1 <= w) => NatRepr w -> A.Domain w -> Integer -> Property
fromArithCorrect w a x =
  A.proper w a ==> A.member a x ==>
    case fromArith w a of
      Nothing -> property True
      Just c -> property (member c (integerToNatural (x .&. maxUnsigned w)))

-- | Converting from Arith to a progression and back is exact: the round-tripped domain
-- contains exactly the same elements as the original.
roundtripArith :: (1 <= w) => NatRepr w -> A.Domain w -> Integer -> Property
roundtripArith w a x =
  A.proper w a ==>
    case fromArith w a of
      Nothing -> property True
      Just c -> property (A.member a x == A.member (toArith c) x)

-- | Every element in a progression is also in its 'toBitwise' conversion.
toBitwiseCorrect :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
toBitwiseCorrect _w c x =
  proper c ==> member c x' ==>
    property (B.member (toBitwise c) (toInteger x'))
  where
    x' = modMask c x

-- | Every element in a bitwise domain is also in its 'fromBitwise' conversion
-- (when that conversion produces a progression).
fromBitwiseCorrect :: (1 <= w) => NatRepr w -> B.Domain w -> Integer -> Property
fromBitwiseCorrect w b x =
  B.proper w b ==> B.member b x ==>
    case fromBitwise w b of
      Nothing -> property True
      Just c -> property (member c (integerToNatural (x .&. maxUnsigned w)))

-- ------------------------------------------------------------------
-- ** Arithmetic

correct_neg :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
correct_neg w c x =
  proper c ==> member c x ==>
    property (member (negate w c) (asN w (Prelude.negate (toInteger x))))

correct_add ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_add w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (add w a b) (asN w (toInteger x + toInteger y)))

correct_sub ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sub w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (sub w a b) (asN w (toInteger x - toInteger y)))

correct_scale ::
  (1 <= w) =>
  NatRepr w -> Integer -> Domain w -> Natural -> Property
correct_scale w k c x =
  proper c ==> member c x ==>
    property (member (scale w k c) (asN w (k * toInteger x)))

correct_mul ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_mul w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (mul w a b) (asN w (toInteger x * toInteger y)))

correct_udiv ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_udiv w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> y /= 0 ==>
    property (member (udiv w a b) (x `quot` y))

correct_urem ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_urem w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> y /= 0 ==>
    property (member (urem w a b) (x `rem` y))

correct_sdiv ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sdiv w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> ys /= 0 ==>
    property (member (sdiv w a b) (asN w (xs `quot` ys)))
  where
    xs = toSigned w (toInteger x)
    ys = toSigned w (toInteger y)

correct_srem ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
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
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_udivSmtlib w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (udivSmtlib w a b) z)
  where
    z = if y == 0
          then fromInteger (maxUnsigned w)
          else x `quot` y

correct_uremSmtlib ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_uremSmtlib w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (uremSmtlib w a b) z)
  where
    z = if y == 0 then x else x `rem` y

correct_sdivSmtlib ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
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
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sremSmtlib w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (sremSmtlib w a b) (asN w z))
  where
    xs = toSigned w (toInteger x)
    ys = toSigned w (toInteger y)
    z  = if ys == 0 then xs else xs `rem` ys

-- ------------------------------------------------------------------
-- ** Bitwise operations

correct_not :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
correct_not w c x =
  proper c ==> member c x ==>
    property (member (not w c) (asN w (Bits.complement (toInteger x))))

correct_and ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_and w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (and w a b) (x Bits..&. y))

correct_or ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_or w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (or w a b) (x Bits..|. y))

correct_xor ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_xor w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (xor w a b) (Bits.xor x y))

-- ------------------------------------------------------------------
-- ** Concatenation, extension, selection, and truncation

correct_zero_ext ::
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Natural -> Property
correct_zero_ext w c u x =
  proper c ==> member c x ==> property (member (zext w c u) x)

correct_sign_ext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Natural -> Property
correct_sign_ext w c u x =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      proper c ==> member c x ==>
        property (member (sext w c u) (asN u (toSigned w (toInteger x))))

correct_concat ::
  forall u v.
  (1 <= u, 1 <= v) =>
  NatRepr u -> Domain u -> Natural ->
  NatRepr v -> Domain v -> Natural ->
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
  NatRepr i -> NatRepr n -> NatRepr w -> Domain w -> Natural -> Property
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
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_shl w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (shl w a b) z)
  where
    s = fromInteger (min (NR.intValue w) (toInteger y))
    z = asN w (toInteger x `Bits.shiftL` s)

correct_lshr ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_lshr w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (lshr w a b) z)
  where
    s = fromInteger (min (NR.intValue w) (toInteger y))
    z = fromInteger (toInteger x `Bits.shiftR` s)

correct_ashr ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_ashr w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (ashr w a b) z)
  where
    s = fromInteger (min (NR.intValue w) (toInteger y))
    z = asN w (toSigned w (toInteger x) `Bits.shiftR` s)

correct_rol ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_rol w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (rol w a b) (fromInteger (Arith.rotateLeft w (toInteger x) (toInteger y))))

correct_ror ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_ror w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (ror w a b) (fromInteger (Arith.rotateRight w (toInteger x) (toInteger y))))

-- ------------------------------------------------------------------
-- ** Lattice operations

-- | 'meet' is sound: every element of both operands is in the result.
correct_meet ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_meet w a x b _y =
  proper a ==> proper b ==> mask a == mask b ==>
    member a x ==> member b x ==>
      case meet w a b of
        Just c  -> property (member c x)
        Nothing -> property False

-- | 'meetPrecise' is sound: every element of both operands is in the result.
correct_meetPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_meetPrecise w a x b _y =
  proper a ==> proper b ==> mask a == mask b ==>
    member a x ==> member b x ==>
      case meetPrecise w a b of
        Just c  -> property (member c x)
        Nothing -> property False

-- | 'meet' is commutative up to 'leqExact' equivalence.
meetCommutative ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
meetCommutative w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    property (eqMaybe (meet w a b) (meet w b a))

-- | 'meetPrecise' is commutative up to 'leqExact' equivalence.
meetPreciseCommutative ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
meetPreciseCommutative w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    property (eqMaybe (meetPrecise w a b) (meetPrecise w b a))

-- | 'meet' is idempotent: @meet a a == Just a@.
meetIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Property
meetIdempotent w a =
  proper a ==> property (meet w a a == Just a)

-- | 'meetPrecise' is idempotent.
meetPreciseIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Property
meetPreciseIdempotent w a =
  proper a ==> property (meetPrecise w a a == Just a)

-- | 'meet' is associative up to 'leqExact' equivalence.
meetAssociative ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Domain w -> Property
meetAssociative w a b c =
  proper a ==> proper b ==> proper c ==>
    mask a == mask b ==> mask b == mask c ==>
      property (eqMaybe (meet w a b >>= meet w c) (meet w b c >>= meet w a))

-- | 'meetPrecise' is associative up to 'leqExact' equivalence.
meetPreciseAssociative ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Domain w -> Property
meetPreciseAssociative w a b c =
  proper a ==> proper b ==> proper c ==>
    mask a == mask b ==> mask b == mask c ==>
      property (eqMaybe (meetPrecise w a b >>= meetPrecise w c)
                        (meetPrecise w b c >>= meetPrecise w a))

-- | 'meetPrecise' refines 'meet': anything 'meetPrecise' contains, 'meet'
-- contains too (modulo emptiness).
meetPreciseRefinesMeet ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
meetPreciseRefinesMeet w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    case (meet w a b, meetPrecise w a b) of
      (Just cM, Just cP) -> property (leqExact cP cM)
      (_, Nothing)       -> property True
      (Nothing, Just _)  -> property False  -- meetPrecise tighter, so this shouldn't happen

-- | 'meet' is monotone in its first argument: if @a `leqExact` b@, then
-- @meet a c `leqMaybe` meet b c@.
meetMonotone ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Domain w -> Property
meetMonotone w a b c =
  proper a ==> proper b ==> proper c ==>
    mask a == mask b ==> mask b == mask c ==>
      leqExact a b ==> property (leqMaybe (meet w a c) (meet w b c))

-- | 'meetPrecise' is monotone in its first argument.
meetPreciseMonotone ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Domain w -> Property
meetPreciseMonotone w a b c =
  proper a ==> proper b ==> proper c ==>
    mask a == mask b ==> mask b == mask c ==>
      leqExact a b ==> property (leqMaybe (meetPrecise w a c) (meetPrecise w b c))

-- | Equality of 'Maybe (Domain w)' under 'leqExact' (i.e., mutual containment).
eqMaybe :: Maybe (Domain w) -> Maybe (Domain w) -> Bool
eqMaybe Nothing Nothing = True
eqMaybe (Just x) (Just y) = leqExact x y && leqExact y x
eqMaybe _ _ = False

-- | @leqMaybe ma mb@: 'Nothing' is bottom; on 'Just' values, 'leqExact'.
leqMaybe :: Maybe (Domain w) -> Maybe (Domain w) -> Bool
leqMaybe Nothing _ = True
leqMaybe (Just _) Nothing = False
leqMaybe (Just x) (Just y) = leqExact x y

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


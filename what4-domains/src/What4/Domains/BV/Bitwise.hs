{-|
Module      : What4.Domains.BV.Bitwise
Copyright   : (c) Galois Inc, 2020
License     : BSD3
Maintainer  : huffman@galois.com

Provides a bitwise implementation of bitvector abstract domains.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module What4.Domains.BV.Bitwise
  ( Domain(..)
  , bitle
  , proper
  , bvdMask
  , member
  , pmember
  , size
  , asSingleton
  , nonempty
  , eq
  , slt
  , ult
  , domainsOverlap
  , bitbounds
  , ubounds
  , sbounds
  -- * Operations
  , any
  , singleton
  , range
  , interval
  , union
  , intersection
  , concat
  , select
  , zext
  , sext
  , testBit
  -- ** shifts and rotates
  , shl
  , lshr
  , ashr
  , rol
  , ror
  -- ** arithmetic
  , add
  , sub
  , negate
  , scale
  , mul
  , udiv
  , urem
  , sdiv
  , srem
  -- ** arithmetic (SMT-LIB div-by-zero semantics)
  , udivSmtlib
  , uremSmtlib
  , sdivSmtlib
  , sremSmtlib
  -- ** bitwise logical
  , and
  , or
  , xor
  , not

  -- * Correctness properties
  , genDomain
  , genElement
  , genPair
  , correct_any
  , correct_singleton
  , correct_overlap
  , correct_union
  , correct_intersection
  , correct_zero_ext
  , correct_sign_ext
  , correct_concat
  , correct_shrink
  , correct_trunc
  , correct_select
  , correct_shl
  , correct_lshr
  , correct_ashr
  , correct_rol
  , correct_ror
  , correct_eq
  , correct_ult
  , correct_slt
  , correct_ubounds
  , correct_sbounds
  , correct_add
  , correct_sub
  , correct_neg
  , correct_scale
  , correct_mul
  , correct_udiv
  , correct_urem
  , correct_sdiv
  , correct_srem
  , correct_udivSmtlib
  , correct_uremSmtlib
  , correct_sdivSmtlib
  , correct_sremSmtlib
  , correct_and
  , correct_or
  , correct_not
  , correct_xor
  , correct_testBit
  ) where

import           Data.Bits hiding (testBit, xor)
import qualified Data.Bits as Bits
import           Data.Parameterized.NatRepr
import           Numeric.Natural
import           GHC.TypeNats
import           What4.Domains.BV.Bitwise.Tnum (Tnum)
import qualified What4.Domains.BV.Bitwise.Tnum as Tnum
import           What4.Domains.Verification (Property, property, (==>), Gen, chooseInteger)

import qualified Prelude
import           Prelude hiding (any, concat, negate, and, or, not)

import qualified What4.Domains.Arithmetic as Arith

-- | A bitwise interval domain, defined via a
--   bitwise upper and lower bound.  The ordering
--   used here to construct the interval is the pointwise
--   ordering on bits.  In particular @x [= y iff x .|. y == y@,
--   and a value @x@ is in the set defined by the pair @(lo,hi)@
--   just when @lo [= x && x [= hi@.
data Domain (w :: Nat) =
  BVBitInterval !Integer !Integer !Integer
  -- ^ @BVDBitInterval mask lo hi@.
  --  @mask@ caches the value of @2^w - 1@
  deriving (Eq, Ord, Show)

-- | /O(w)/. Test if the domain satisfies its invariants.
proper :: NatRepr w -> Domain w -> Bool
proper w (BVBitInterval mask lo hi) =
  mask == maxUnsigned w &&
  bitle lo mask &&
  bitle hi mask &&
  bitle lo hi

-- | /O(w)/. Test if the given integer value is a member of the abstract domain.
member :: Domain w -> Integer -> Bool
member (BVBitInterval mask lo hi) x = bitle lo x' && bitle x' hi
  where x' = x .&. mask

-- | /O(w)/. Compute how many concrete elements are in the abstract domain.
size :: Domain w -> Integer
size (BVBitInterval _ lo hi)
  | bitle lo hi = Bits.bit p
  | otherwise   = 0
 where
 u = Bits.xor lo hi
 p = Bits.popCount u

bitle :: Integer -> Integer -> Bool
bitle x y = (x .|. y) == y

-- | /O(1)/. Return the bitvector mask value from this domain.
bvdMask :: Domain w -> Integer
bvdMask (BVBitInterval mask _ _) = mask

-- | Random generator for domain values.  We always generate
--   nonempty domain values.
genDomain :: NatRepr w -> Gen (Domain w)
genDomain w =
  do let mask = maxUnsigned w
     lo <- chooseInteger (0, mask)
     hi <- chooseInteger (0, mask)
     pure $! interval mask lo (lo .|. hi)

-- This generator goes to some pains to try
-- to generate a good statistical distribution
-- of the values in the domain.  It only chooses
-- random bits for the "unknown" values of
-- the domain, then stripes them out among
-- the unknown bit positions.
genElement :: Domain w -> Gen Integer
genElement (BVBitInterval _mask lo hi) =
  do x <- chooseInteger (0, bit bs - 1)
     pure $ stripe lo x 0

 where
 u = Bits.xor lo hi
 bs = Bits.popCount u
 stripe val x i
   | x == 0 = val
   | Bits.testBit u i =
       let val' = if Bits.testBit x 0 then setBit val i else val in
       stripe val' (x `shiftR` 1) (i + 1)
   | otherwise = stripe val x (i + 1)

{- A faster generator, but I worry that it
   doesn't have very good statistical properties...

genElement :: Domain w -> Gen Integer
genElement (BVBitInterval mask lo hi) =
  do let u = Bits.xor lo hi
     x <- chooseInteger (0, mask)
     pure ((x .&. u) .|. lo)
-}

-- | Generate a random nonempty domain and an element
--   contained in that domain.
genPair :: NatRepr w -> Gen (Domain w, Integer)
genPair w =
  do a <- genDomain w
     x <- genElement a
     return (a,x)

-- | /O(1)/. Unsafe constructor for internal use.
interval :: Integer -> Integer -> Integer -> Domain w
interval mask lo hi = BVBitInterval mask lo hi

-- | /O(w)/. Construct a domain from bitwise lower and upper bounds.
range :: NatRepr w -> Integer -> Integer -> Domain w
range w lo hi = BVBitInterval (maxUnsigned w) lo' hi'
  where
  lo'  = lo .&. mask
  hi'  = hi .&. mask
  mask = maxUnsigned w

-- | /O(1)/. Bitwise lower and upper bounds.
bitbounds :: Domain w -> (Integer, Integer)
bitbounds (BVBitInterval _ lo hi) = (lo, hi)

-- | /O(w)/. Test if this domain contains a single value, and return it if so.
asSingleton :: Domain w -> Maybe Integer
asSingleton (BVBitInterval _ lo hi) = if lo == hi then Just lo else Nothing

-- | /O(w)/. Returns true iff there is at least one element
-- in this bitwise domain.
nonempty :: Domain w -> Bool
nonempty (BVBitInterval _mask lo hi) = bitle lo hi

-- | /O(w)/. Return a domain containing just the given value.
singleton :: NatRepr w -> Integer -> Domain w
singleton w x = BVBitInterval mask x' x'
  where
  x' = x .&. mask
  mask = maxUnsigned w

-- | /O(w)/. Bitwise domain containing every bitvector value.
any :: NatRepr w -> Domain w
any w = BVBitInterval mask 0 mask
  where
  mask = maxUnsigned w

-- | /O(w)/. Returns true iff the domains have some value in common.
domainsOverlap :: Domain w -> Domain w -> Bool
domainsOverlap a b = nonempty (intersection a b)

-- | /O(w)/. Decide equality of two domains: 'Just True' if both are the same
-- singleton, 'Just False' if they're disjoint, 'Nothing' otherwise.
eq :: Domain w -> Domain w -> Maybe Bool
eq a b
  | Just x <- asSingleton a
  , Just y <- asSingleton b
  = Just (x == y)

  | Prelude.not (domainsOverlap a b) = Just False
  | otherwise = Nothing

-- | /O(w)/. Greatest lower bound of two domains.
intersection :: Domain w -> Domain w -> Domain w
intersection (BVBitInterval mask alo ahi) (BVBitInterval _ blo bhi) =
  BVBitInterval mask (alo .|. blo) (ahi .&. bhi)

-- | /O(w)/. Least upper bound of two domains.
union :: Domain w -> Domain w -> Domain w
union (BVBitInterval mask alo ahi) (BVBitInterval _ blo bhi) =
  BVBitInterval mask (alo .&. blo) (ahi .|. bhi)

-- | /O(u + v)/. @concat a y@ returns a domain where each element in @a@ has
-- been concatenated with an element in @y@. The most-significant bits are
-- @a@, and the least significant bits are @y@.
concat :: NatRepr u -> Domain u -> NatRepr v -> Domain v -> Domain (u + v)
concat u (BVBitInterval _ alo ahi) v (BVBitInterval _ blo bhi) =
    BVBitInterval mask (cat alo blo) (cat ahi bhi)
  where
    cat i j = (i `shiftL` widthVal v) + j
    mask = maxUnsigned (addNat u v)

-- | /O(w)/. @shrink i a@ drops the @i@ least significant bits from @a@.
shrink ::
  NatRepr i ->
  Domain (i + n) -> Domain n
shrink i (BVBitInterval mask lo hi) = BVBitInterval (shr mask) (shr lo) (shr hi)
  where
  shr x = x `shiftR` widthVal i

-- | /O(w)/. @trunc n d@ selects the @n@ least significant bits from @d@.
trunc ::
  (n <= w) =>
  NatRepr n ->
  Domain w ->
  Domain n
trunc n (BVBitInterval _ lo hi) = range n lo hi

-- | /O(w)/. @select i n a@ selects @n@ bits starting from index @i@ from @a@.
select ::
  (1 <= n, i + n <= w) =>
  NatRepr i ->
  NatRepr n ->
  Domain w -> Domain n
select i n a = shrink i (trunc (addNat i n) a)

-- | /O(w)/. Zero-extend a domain to a larger width.
zext :: (1 <= w, w + 1 <= u) => Domain w -> NatRepr u -> Domain u
zext (BVBitInterval _ lo hi) u = range u lo hi

-- | /O(w)/. Sign-extend a domain to a larger width.
sext :: (1 <= w, w + 1 <= u) => NatRepr w -> Domain w -> NatRepr u -> Domain u
sext w (BVBitInterval _ lo hi) u = range u lo' hi'
  where
  lo' = toSigned w lo
  hi' = toSigned w hi

-- | /O(w)/. Test bit @i@ of every value in the domain: 'Just True' if it is
-- set in every member, 'Just False' if clear in every member, 'Nothing' if
-- it varies.
testBit :: Domain w -> Natural -> Maybe Bool
testBit (BVBitInterval _mask lo hi) i = if lob == hib then Just lob else Nothing
  where
  lob = Bits.testBit lo j
  hib = Bits.testBit hi j
  j = fromIntegral i

-- | /O(w)/. Shift left by a known amount.
shl :: NatRepr w -> Domain w -> Integer -> Domain w
shl w (BVBitInterval mask lo hi) y = BVBitInterval mask (shleft lo) (shleft hi)
  where
  y' = fromInteger (min y (intValue w))
  shleft x = (x `shiftL` y') .&. mask

-- | /O(w)/. Rotate left by a known amount.
rol :: NatRepr w -> Domain w -> Integer -> Domain w
rol w (BVBitInterval mask lo hi) y =
  BVBitInterval mask (Arith.rotateLeft w lo y) (Arith.rotateLeft w hi y)

-- | /O(w)/. Rotate right by a known amount.
ror :: NatRepr w -> Domain w -> Integer -> Domain w
ror w (BVBitInterval mask lo hi) y =
  BVBitInterval mask (Arith.rotateRight w lo y) (Arith.rotateRight w hi y)

-- | /O(w)/. Logical (zero-fill) shift right by a known amount.
lshr :: NatRepr w -> Domain w -> Integer -> Domain w
lshr w (BVBitInterval mask lo hi) y = BVBitInterval mask (shr lo) (shr hi)
  where
  y' = fromInteger (min y (intValue w))
  shr x = x `shiftR` y'

-- | /O(w)/. Arithmetic (sign-extending) shift right by a known amount.
ashr :: (1 <= w) => NatRepr w -> Domain w -> Integer -> Domain w
ashr w (BVBitInterval mask lo hi) y = BVBitInterval mask (shr lo) (shr hi)
  where
  y' = fromInteger (min y (intValue w))
  shr x = ((toSigned w x) `shiftR` y') .&. mask

-- | /O(w)/. Bitwise complement.
not :: Domain w -> Domain w
not (BVBitInterval mask alo ahi) =
  BVBitInterval mask (ahi `Bits.xor` mask) (alo `Bits.xor` mask)

-- | /O(w)/. Bitwise AND of two domains.
and :: Domain w -> Domain w -> Domain w
and (BVBitInterval mask alo ahi) (BVBitInterval _ blo bhi) =
  BVBitInterval mask (alo .&. blo) (ahi .&. bhi)

-- | /O(w)/. Bitwise OR of two domains.
or :: Domain w -> Domain w -> Domain w
or (BVBitInterval mask alo ahi) (BVBitInterval _ blo bhi) =
  BVBitInterval mask (alo .|. blo) (ahi .|. bhi)

-- | /O(w)/. Bitwise XOR of two domains.
xor :: Domain w -> Domain w -> Domain w
xor (BVBitInterval mask alo ahi) (BVBitInterval _ blo bhi) = BVBitInterval mask clo chi
  where
  au  = alo `Bits.xor` ahi
  bu  = blo `Bits.xor` bhi
  c   = alo `Bits.xor` blo
  cu  = au .|. bu
  chi = c  .|. cu
  clo = chi `Bits.xor` cu


---------------------------------------------------------------------------------------
-- Bounds and comparisons

-- | /O(1)/. Unsigned bounds for the domain. The low bit-pattern bound is
-- also the unsigned minimum, and the high bit-pattern bound is also the
-- unsigned maximum: setting unknown bits to 0 minimizes, setting them to
-- 1 maximizes.
ubounds :: Domain w -> (Integer, Integer)
ubounds = bitbounds

-- | /O(w)/. Signed bounds for the domain.
sbounds :: (1 <= w) => NatRepr w -> Domain w -> (Integer, Integer)
sbounds w (BVBitInterval _ lo hi) = (toSigned w lo', toSigned w hi')
  where
  signbit = bit (widthVal w - 1)
  -- If the sign bit is known (lo and hi agree on it), the bit-pattern
  -- bounds are also the signed bounds. If the sign bit is unknown, the
  -- most-negative value sets the sign bit and clears all other unknowns,
  -- and the most-positive clears the sign bit and sets all other unknowns.
  (lo', hi')
    | (lo .&. signbit) == (hi .&. signbit) = (lo, hi)
    | otherwise = (lo .|. signbit, hi .&. complement signbit)

-- | /O(w)/. Check if all elements in one domain are unsigned-less-than all
-- elements in the other.
ult :: Domain w -> Domain w -> Maybe Bool
ult a b
  | ah < bl  = Just True
  | al >= bh = Just False
  | otherwise = Nothing
  where
  (al, ah) = ubounds a
  (bl, bh) = ubounds b

-- | /O(w)/. Check if all elements in one domain are signed-less-than all
-- elements in the other.
slt :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe Bool
slt w a b
  | ah < bl  = Just True
  | al >= bh = Just False
  | otherwise = Nothing
  where
  (al, ah) = sbounds w a
  (bl, bh) = sbounds w b

---------------------------------------------------------------------------------------
-- Arithmetic

-- | Convert a domain into its tristate-number form.
toTnum :: Domain w -> Tnum
toTnum (BVBitInterval _ lo hi) = Tnum.mk lo (lo `Bits.xor` hi)

-- | Convert a tristate-number back into a domain at the given @bvmask@.
fromTnum :: Integer -> Tnum -> Domain w
fromTnum mask t = BVBitInterval mask v (v .|. Tnum.tnumMask t)
  where v = Tnum.tnumValue t

-- | Internal helper: build a singleton domain when only the mask is known.
mkSingleton :: Integer -> Integer -> Domain w
mkSingleton mask x = BVBitInterval mask x' x'
  where x' = x .&. mask

-- | /O(w)/. Add two bitwise domains.
add :: Domain w -> Domain w -> Domain w
add a@(BVBitInterval mask _ _) b = fromTnum mask (Tnum.add mask (toTnum a) (toTnum b))

-- | /O(w)/. Two's complement negation: @negate a = not a + 1@.
negate :: Domain w -> Domain w
negate a = add (not a) (mkSingleton (bvdMask a) 1)

-- | /O(w)/. Subtract: @sub a b = add a (negate b)@.
sub :: Domain w -> Domain w -> Domain w
sub a b = add a (negate b)

-- | /O(w²)/. Multiply by a constant.
scale :: Integer -> Domain w -> Domain w
scale k a = mul (mkSingleton (bvdMask a) k) a

-- | /O(w²)/. Multiply two bitwise domains via the shift-and-add
-- tristate-number algorithm (BPF @tnum_mul@).
mul :: Domain w -> Domain w -> Domain w
mul a@(BVBitInterval mask _ _) b =
  fromTnum mask (Tnum.mul mask (toTnum a) (toTnum b))

-- | /O(w)/. Unsigned division. Assumes the divisor is nonzero.
--
-- Compared to the arithmetic-domain @udiv@, this can be more precise when the
-- divisor is a known power of two: the result is exact, and bit-level structure
-- of the dividend is preserved (e.g.\ @udiv (any w) (singleton w (2^k))@ has
-- its top @k@ bits known zero).
udiv :: Domain w -> Domain w -> Domain w
udiv a@(BVBitInterval mask _ _) b =
  fromTnum mask (Tnum.udiv mask (toTnum a) (toTnum b))

-- | /O(w)/. Unsigned remainder. Assumes the divisor is nonzero.
--
-- Like 'udiv', this is more precise when the divisor is a known power of two:
-- @urem a (singleton w (2^k))@ is exactly the low @k@ bits of @a@.
urem :: Domain w -> Domain w -> Domain w
urem a@(BVBitInterval mask _ _) b =
  fromTnum mask (Tnum.urem mask (toTnum a) (toTnum b))

-- | /O(w)/. Signed division (rounds toward zero). Assumes the divisor is
-- nonzero.
--
-- Implemented by splitting each operand on its sign bit into a non-negative
-- \"zero circle\" and a negative \"one circle\", applying 'udiv' to the
-- absolute values, fixing up the sign, and joining the resulting subcases.
sdiv :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sdiv w = signedOp w udiv flipDiff
  where
  -- For sdiv, the result is negated iff the input signs differ.
  flipDiff sa sb d = if sa == sb then d else negate d

-- | /O(w)/. Signed remainder (sign of dividend). Assumes the divisor is
-- nonzero.
--
-- Implemented like 'sdiv', except the result takes the sign of the dividend
-- rather than the XOR of the input signs.
srem :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
srem w = signedOp w urem flipByDividend
  where
  -- For srem, the result has the sign of the dividend.
  flipByDividend SNeg _ d = negate d
  flipByDividend SNonneg _ d = d

-- | Helper for signed div/rem: split each operand on its sign bit,
--   call the unsigned operation on the absolute values, fix up the
--   result's sign per the operation's rule, and union all subcases.
signedOp ::
  (1 <= w) =>
  NatRepr w ->
  (Domain w -> Domain w -> Domain w) {- ^ unsigned op on absolute values -} ->
  (Sign -> Sign -> Domain w -> Domain w) {- ^ result fix-up given signs -} ->
  Domain w -> Domain w ->
  Domain w
signedOp w uop fixup a b =
  Prelude.foldr1 union
    [ fixup sa sb (uop (absVal sa a') (absVal sb b'))
    | (sa, a') <- splitSign w a
    , (sb, b') <- splitSign w b
    ]
  where
  absVal SNonneg d = d
  absVal SNeg    d = negate d

data Sign = SNonneg | SNeg
  deriving Eq

-- | If the sign bit is known, return its value; otherwise 'Nothing'.
signOf :: (1 <= w) => NatRepr w -> Domain w -> Maybe Sign
signOf w (BVBitInterval _ lo hi)
  | Bits.testBit lo i && Bits.testBit hi i = Just SNeg
  | Prelude.not (Bits.testBit lo i || Bits.testBit hi i) = Just SNonneg
  | otherwise = Nothing
  where i = widthVal w - 1

-- | Split a domain on its sign bit, returning each restriction tagged with
--   its sign. If the sign bit is already known, returns a singleton list.
splitSign :: (1 <= w) => NatRepr w -> Domain w -> [(Sign, Domain w)]
splitSign w d@(BVBitInterval mask lo hi) =
  case signOf w d of
    Just s  -> [(s, d)]
    Nothing -> [ (SNonneg, BVBitInterval mask lo (hi `Bits.xor` signbit))
               , (SNeg,    BVBitInterval mask (lo .|. signbit) hi)
               ]
  where
  signbit = bit (widthVal w - 1)

-- | /O(w)/. Like 'udiv', but using the SMT-LIB @FixedSizeBitVectors@ theory's
-- div-by-zero semantics: @bvudiv s 0@ is the all-ones bitvector. See @Note
-- [SMT-LIB division]@ in "What4.Interface" for the design rationale.
udivSmtlib :: (1 <= w) => Domain w -> Domain w -> Domain w
udivSmtlib a b
  | Just 0 <- asSingleton b = mkSingleton mask mask
  | member b 0              = union (udiv a b) (mkSingleton mask mask)
  | otherwise               = udiv a b
  where
  mask = bvdMask a

-- | /O(w)/. Like 'urem', but using the SMT-LIB @FixedSizeBitVectors@ theory's
-- div-by-zero semantics: @bvurem s 0@ is the dividend itself (@s@). See @Note
-- [SMT-LIB division]@ in "What4.Interface" for the design rationale.
uremSmtlib :: (1 <= w) => Domain w -> Domain w -> Domain w
uremSmtlib a b
  | Just 0 <- asSingleton b = a
  | member b 0              = union (urem a b) a
  | otherwise               = urem a b

-- | /O(w)/. Like 'sdiv', but using the SMT-LIB QF_BV logic's div-by-zero
-- convention: @bvsdiv s 0@ is all-ones when @s@ is non-negative and @1@
-- when @s@ is negative. See @Note [SMT-LIB division]@ in "What4.Interface"
-- for the design rationale.
sdivSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sdivSmtlib w a b
  | Just 0 <- asSingleton b = sdivByZero w a
  | member b 0              = union (sdiv w a b) (sdivByZero w a)
  | otherwise               = sdiv w a b

-- | The result of @bvsdiv s 0@ as a function of @s@'s sign: all-ones when @s >=
--   0@, @1@ when @s < 0@.
sdivByZero :: (1 <= w) => NatRepr w -> Domain w -> Domain w
sdivByZero w a =
  case signOf w a of
    Just SNonneg -> mkSingleton mask mask
    Just SNeg    -> mkSingleton mask 1
    Nothing      -> union (mkSingleton mask 1) (mkSingleton mask mask)
  where
  mask = bvdMask a

-- | /O(w)/. Like 'srem', but using the SMT-LIB QF_BV logic's div-by-zero
-- convention: @bvsrem s 0@ is the dividend itself (@s@). See @Note
-- [SMT-LIB division]@ in "What4.Interface" for the design rationale.
sremSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sremSmtlib w a b
  | Just 0 <- asSingleton b = a
  | member b 0              = union (srem w a b) a
  | otherwise               = srem w a b


---------------------------------------------------------------------------------------
-- Correctness properties

-- | Check that a domain is proper, and that
--   the given value is a member
pmember :: NatRepr n -> Domain n -> Integer -> Bool
pmember n a x = proper n a && member a x

correct_any :: (1 <= n) => NatRepr n -> Integer -> Property
correct_any n x = property (pmember n (any n) x)

correct_singleton :: (1 <= n) => NatRepr n -> Integer -> Integer -> Property
correct_singleton n x y = property (pmember n (singleton n x') y' == (x' == y'))
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_overlap :: Domain n -> Domain n -> Integer -> Property
correct_overlap a b x =
  member a x && member b x ==> domainsOverlap a b

correct_union :: (1 <= n) => NatRepr n -> Domain n -> Domain n -> Integer -> Property
correct_union n a b x =
  member a x || member b x ==> pmember n (union a b) x

correct_intersection :: (1 <= n) => Domain n -> Domain n -> Integer -> Property
correct_intersection a b x = -- NB, intersection might not be proper
  member a x && member b x ==> member (intersection a b) x

correct_zero_ext :: (1 <= w, w + 1 <= u) => NatRepr w -> Domain w -> NatRepr u -> Integer -> Property
correct_zero_ext w a u x = member a x' ==> pmember u (zext a u) x'
  where
  x' = toUnsigned w x

correct_sign_ext :: (1 <= w, w + 1 <= u) => NatRepr w -> Domain w -> NatRepr u -> Integer -> Property
correct_sign_ext w a u x = member a x' ==> pmember u (sext w a u) x'
  where
  x' = toSigned w x

correct_concat :: NatRepr m -> (Domain m,Integer) -> NatRepr n -> (Domain n,Integer) -> Property
correct_concat m (a,x) n (b,y) = member a x' ==> member b y' ==> pmember (addNat m n) (concat m a n b) z
  where
  x' = toUnsigned m x
  y' = toUnsigned n y
  z  = x' `shiftL` (widthVal n) .|. y'

correct_shrink :: NatRepr i -> NatRepr n -> (Domain (i + n), Integer) -> Property
correct_shrink i n (a,x) = member a x' ==> pmember n (shrink i a) (x' `shiftR` widthVal i)
  where
  x' = x .&. bvdMask a

correct_trunc :: (n <= w) => NatRepr n -> (Domain w, Integer) -> Property
correct_trunc n (a,x) = member a x' ==> pmember n (trunc n a) (toUnsigned n x')
  where
  x' = x .&. bvdMask a

correct_select :: (1 <= n, i + n <= w) =>
  NatRepr i -> NatRepr n -> (Domain w, Integer) -> Property
correct_select i n (a, x) = member a x ==> pmember n (select i n a) y
  where
  y = toUnsigned n ((x .&. bvdMask a) `shiftR` (widthVal i))

correct_eq :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_eq n (a,x) (b,y) =
  member a x ==> member b y ==>
    case eq a b of
      Just True  -> toUnsigned n x == toUnsigned n y
      Just False -> toUnsigned n x /= toUnsigned n y
      Nothing    -> True

correct_shl :: (1 <= n) => NatRepr n -> (Domain n,Integer) -> Integer -> Property
correct_shl n (a,x) y = member a x ==> pmember n (shl n a y) z
  where
  z = (toUnsigned n x) `shiftL` fromInteger (min (intValue n) y)

correct_lshr :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Integer -> Property
correct_lshr n (a,x) y = member a x ==> pmember n (lshr n a y) z
  where
  z = (toUnsigned n x) `shiftR` fromInteger (min (intValue n) y)

correct_ashr :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Integer -> Property
correct_ashr n (a,x) y = member a x ==> pmember n (ashr n a y) z
  where
  z = (toSigned n x) `shiftR` fromInteger (min (intValue n) y)

correct_rol :: (1 <= n) => NatRepr n -> (Domain n,Integer) -> Integer -> Property
correct_rol n (a,x) y = member a x ==> pmember n (rol n a y) (Arith.rotateLeft n x y)

correct_ror :: (1 <= n) => NatRepr n -> (Domain n,Integer) -> Integer -> Property
correct_ror n (a,x) y = member a x ==> pmember n (ror n a y) (Arith.rotateRight n x y)

correct_not :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Property
correct_not n (a,x) = member a x ==> pmember n (not a) (complement x)

correct_and :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_and n (a,x) (b,y) = member a x ==> member b y ==> pmember n (and a b) (x .&. y)

correct_or :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_or n (a,x) (b,y) = member a x ==> member b y ==> pmember n (or a b) (x .|. y)

correct_xor :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_xor n (a,x) (b,y) = member a x ==> member b y ==> pmember n (xor a b) (x `Bits.xor` y)

correct_testBit :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Natural -> Property
correct_testBit n (a,x) i =
  i < natValue n ==>
    case testBit a i of
      Just True  -> Bits.testBit x (fromIntegral i)
      Just False -> Prelude.not (Bits.testBit x (fromIntegral i))
      Nothing    -> True

correct_ubounds :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Property
correct_ubounds n (a,x) = member a x' ==> lo <= x' && x' <= hi
  where
  x' = toUnsigned n x
  (lo, hi) = ubounds a

correct_sbounds :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Property
correct_sbounds n (a,x) = member a x' ==> lo <= x' && x' <= hi
  where
  x' = toSigned n x
  (lo, hi) = sbounds n a

correct_ult :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_ult n (a,x) (b,y) =
  member a x ==> member b y ==>
    case ult a b of
      Just True  -> toUnsigned n x < toUnsigned n y
      Just False -> toUnsigned n x >= toUnsigned n y
      Nothing    -> True

correct_slt :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_slt n (a,x) (b,y) =
  member a x ==> member b y ==>
    case slt n a b of
      Just True  -> toSigned n x < toSigned n y
      Just False -> toSigned n x >= toSigned n y
      Nothing    -> True

correct_add :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_add n (a,x) (b,y) = member a x ==> member b y ==> pmember n (add a b) (x + y)

correct_sub :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_sub n (a,x) (b,y) = member a x ==> member b y ==> pmember n (sub a b) (x - y)

correct_neg :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Property
correct_neg n (a,x) = member a x ==> pmember n (negate a) (Prelude.negate x)

correct_scale :: (1 <= n) => NatRepr n -> Integer -> (Domain n, Integer) -> Property
correct_scale n k (a,x) = member a x ==> pmember n (scale k' a) (k' * x)
  where
  k' = toSigned n k

correct_mul :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_mul n (a,x) (b,y) = member a x ==> member b y ==> pmember n (mul a b) (x * y)

correct_udiv :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_udiv n (a,x) (b,y) =
  member a x ==> member b y ==> y' /= 0 ==> pmember n (udiv a b) (x' `quot` y')
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_urem :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_urem n (a,x) (b,y) =
  member a x ==> member b y ==> y' /= 0 ==> pmember n (urem a b) (x' `rem` y')
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_sdiv :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_sdiv n (a,x) (b,y) =
  member a x ==> member b y ==> y' /= 0 ==> pmember n (sdiv n a b) (x' `quot` y')
  where
  x' = toSigned n x
  y' = toSigned n y

correct_srem :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_srem n (a,x) (b,y) =
  member a x ==> member b y ==> y' /= 0 ==> pmember n (srem n a b) (x' `rem` y')
  where
  x' = toSigned n x
  y' = toSigned n y

correct_udivSmtlib ::
  (1 <= n) =>
  NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_udivSmtlib n (a,x) (b,y) =
  member a x' ==> member b y' ==>
    pmember n (udivSmtlib a b)
      (if y' == 0 then maxUnsigned n else x' `quot` y')
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_uremSmtlib ::
  (1 <= n) =>
  NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_uremSmtlib n (a,x) (b,y) =
  member a x' ==> member b y' ==>
    pmember n (uremSmtlib a b) (if y' == 0 then x' else x' `rem` y')
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_sdivSmtlib ::
  (1 <= n) =>
  NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_sdivSmtlib n (a,x) (b,y) =
  member a x ==> member b y ==>
    pmember n (sdivSmtlib n a b) result
  where
  x' = toSigned n x
  y' = toSigned n y
  result
    | y' /= 0   = x' `quot` y'
    | x' >= 0   = maxUnsigned n
    | otherwise = 1

correct_sremSmtlib ::
  (1 <= n) =>
  NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_sremSmtlib n (a,x) (b,y) =
  member a x ==> member b y ==>
    pmember n (sremSmtlib n a b) (if y' == 0 then x' else x' `rem` y')
  where
  x' = toSigned n x
  y' = toSigned n y


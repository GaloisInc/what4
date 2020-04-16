{-|
Module      : What4.Utils.BVDomain.Arith
Copyright   : (c) Galois Inc, 2019
License     : BSD3
Maintainer  : huffman@galois.com

Provides an interval-based implementation of bitvector abstract
domains.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module What4.Utils.BVDomain.Arith
  ( Domain(..)
  , proper
  , bvdMask
  , member
  , pmember
  , interval
  -- * Projection functions
  , asSingleton
  , ubounds
  , sbounds
  , eq
  , slt
  , ult
  , domainsOverlap
  , arithDomainData
  , bitbounds
  , unknowns
    -- * Operations
  , any
  , singleton
  , range
  , fromAscEltList
  , union
  , concat
  , select
  , zext
  , sext
    -- ** Shifts
  , shl
  , lshr
  , ashr
    -- ** Arithmetic
  , add
  , negate
  , scale
  , mul
  , udiv
  , urem
  , sdiv
  , srem
    -- ** Bitwise
  , What4.Utils.BVDomain.Arith.not

  -- * Correctness properties
  , genDomain
  , genElement
  , genPair
  , correct_any
  , correct_ubounds
  , correct_sbounds
  , correct_singleton
  , correct_overlap
  , correct_union
  , correct_zero_ext
  , correct_sign_ext
  , correct_concat
  , correct_shrink
  , correct_trunc
  , correct_select
  , correct_add
  , correct_neg
  , correct_mul
  , correct_udiv
  , correct_urem
  , correct_sdivRange
  , correct_sdiv
  , correct_srem
  , correct_not
  , correct_shl
  , correct_lshr
  , correct_ashr
  , correct_eq
  , correct_ult
  , correct_slt
  , correct_unknowns
  , correct_bitbounds
  ) where

import qualified Data.Bits as Bits
import           Data.Bits hiding (testBit, xor)
import           Data.Parameterized.NatRepr
import           GHC.TypeNats
import           GHC.Stack

import qualified Prelude
import           Prelude hiding (any, concat, negate, and, or, not)

import           Test.QuickCheck (Property, property, (==>), Gen, chooseInteger)

--------------------------------------------------------------------------------
-- BVDomain definition

-- | A value of type @'BVDomain' w@ represents a set of bitvectors of
-- width @w@. Each 'BVDomain' can represent a single contiguous
-- interval of bitvectors that may wrap around from -1 to 0.
data Domain (w :: Nat)
  = BVDAny !Integer
  -- ^ The set of all bitvectors of width @w@. Argument caches @2^w-1@.
  | BVDInterval !Integer !Integer !Integer
  -- ^ Intervals are represented by a starting value and a size.
  -- @BVDInterval mask l d@ represents the set of values of the form
  -- @x mod 2^w@ for @x@ such that @l <= x <= l + d@. It should
  -- satisfy the invariants @0 <= l < 2^w@ and @0 <= d < 2^w@. The
  -- first argument caches the value @2^w-1@.
  deriving Show

member :: Domain w -> Integer -> Bool
member (BVDAny _) _ = True
member (BVDInterval mask lo sz) x = ((x' - lo) .&. mask) <= sz
  where x' = x .&. mask

-- | Check if the domain satisfies its invariants
proper :: NatRepr w -> Domain w -> Bool
proper w (BVDAny mask) = mask == maxUnsigned w
proper w (BVDInterval mask lo sz) =
  mask == maxUnsigned w &&
  lo .|. mask == mask &&
  sz .|. mask == mask &&
  sz < mask

bvdMask :: Domain w -> Integer
bvdMask x =
  case x of
    BVDAny mask -> mask
    BVDInterval mask _ _ -> mask

-- | Random generator for domain values
genDomain :: NatRepr w -> Gen (Domain w)
genDomain w =
  do let mask = maxUnsigned w
     lo <- chooseInteger (0, mask)
     sz <- chooseInteger (0, mask)
     pure $! interval mask lo sz

genElement :: Domain w -> Gen Integer
genElement (BVDAny mask) = chooseInteger (0, mask)
genElement (BVDInterval mask lo sz) =
   do x <- chooseInteger (0, sz)
      pure ((x+lo) .&. mask)

genPair :: NatRepr w -> Gen (Domain w, Integer)
genPair w =
  do a <- genDomain w
     x <- genElement a
     return (a,x)

--------------------------------------------------------------------------------

-- | @halfRange n@ returns @2^(n-1)@.
halfRange :: (1 <= w) => NatRepr w -> Integer
halfRange w = bit (widthVal w - 1)

--------------------------------------------------------------------------------
-- Projection functions

-- | Return value if this is a singleton.
asSingleton :: Domain w -> Maybe Integer
asSingleton x =
  case x of
    BVDAny _ -> Nothing
    BVDInterval _ xl xd
      | xd == 0 -> Just xl
      | otherwise -> Nothing

isSingletonZero :: Domain w -> Bool
isSingletonZero x =
  case x of
    BVDInterval _ 0 0 -> True
    _ -> False

isBVDAny :: Domain w -> Bool
isBVDAny x =
  case x of
    BVDAny {} -> True
    BVDInterval {} -> False

-- | Return unsigned bounds for domain.
ubounds :: Domain w -> (Integer, Integer)
ubounds a =
  case a of
    BVDAny mask -> (0, mask)
    BVDInterval mask al aw
      | ah > mask -> (0, mask)
      | otherwise -> (al, ah)
      where ah = al + aw

-- | Return signed bounds for domain.
sbounds :: (1 <= w) => NatRepr w -> Domain w -> (Integer, Integer)
sbounds w a = (lo - delta, hi - delta)
  where
    delta = halfRange w
    (lo, hi) = ubounds (add a (BVDInterval (bvdMask a) delta 0))

-- | Return the @(lo,sz)@, the low bound and size
--   of the given arithmetic interval.  A value @x@ is in
--   the set defined by this domain iff
--   @(x - lo) `mod` w <= sz@ holds.
--   Returns @Nothing@ if the domain contains all values.
arithDomainData :: Domain w -> Maybe (Integer, Integer)
arithDomainData (BVDAny _) = Nothing
arithDomainData (BVDInterval _ al aw) = Just (al, aw)

-- | Return true if domains contain a common element.
domainsOverlap :: Domain w -> Domain w -> Bool
domainsOverlap a b =
  case a of
    BVDAny _ -> True
    BVDInterval _ al aw ->
      case b of
        BVDAny _ -> True
        BVDInterval mask bl bw ->
          diff <= bw || diff + aw > mask
          where diff = (al - bl) .&. mask

eq :: Domain w -> Domain w -> Maybe Bool
eq a b
  | Just x <- asSingleton a
  , Just y <- asSingleton b = Just (x == y)
  | domainsOverlap a b == False = Just False
  | otherwise = Nothing

-- | Check if all elements in one domain are less than all elements in other.
slt :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe Bool
slt w a b
  | a_max < b_min = Just True
  | a_min >= b_max = Just False
  | otherwise = Nothing
  where
    (a_min, a_max) = sbounds w a
    (b_min, b_max) = sbounds w b

-- | Check if all elements in one domain are less than all elements in other.
ult :: (1 <= w) => Domain w -> Domain w -> Maybe Bool
ult a b
  | a_max < b_min = Just True
  | a_min >= b_max = Just False
  | otherwise = Nothing
  where
    (a_min, a_max) = ubounds a
    (b_min, b_max) = ubounds b

--------------------------------------------------------------------------------
-- Operations

-- | Represents all values
any :: (1 <= w) => NatRepr w -> Domain w
any w = BVDAny (maxUnsigned w)

-- | Create a bitvector domain representing the integer.
singleton :: (HasCallStack, 1 <= w) => NatRepr w -> Integer -> Domain w
singleton w x = BVDInterval mask (x .&. mask) 0
  where mask = maxUnsigned w

-- | @range w l u@ returns domain containing all bitvectors formed
-- from the @w@ low order bits of some @i@ in @[l,u]@.  Note that per
-- @testBit@, the least significant bit has index @0@.
range :: NatRepr w -> Integer -> Integer -> Domain w
range w al ah = interval mask al ((ah - al) .&. mask)
  where mask = maxUnsigned w

-- | Unsafe constructor for internal use only. Caller must ensure that
-- @mask = maxUnsigned w@, and that @aw@ is non-negative.
interval :: Integer -> Integer -> Integer -> Domain w
interval mask al aw =
  if aw >= mask then BVDAny mask else BVDInterval mask (al .&. mask) aw

-- | Create an abstract domain from an ascending list of elements.
-- The elements are assumed to be distinct.
fromAscEltList :: (1 <= w) => NatRepr w -> [Integer] -> Domain w
fromAscEltList w [] = singleton w 0
fromAscEltList w [x] = singleton w x
fromAscEltList w (x0 : x1 : xs) = go (x0, x0) (x1, x1) xs
  where
    -- Invariant: the gap between @b@ and @c@ is the biggest we've
    -- seen between adjacent values so far.
    go (a, b) (c, d) [] = union (range w a b) (range w c d)
    go (a, b) (c, d) (e : rest)
      | e - d > c - b = go (a, d) (e, e) rest
      | otherwise     = go (a, b) (c, e) rest

-- | Return union of two domains.
union :: (1 <= w) => Domain w -> Domain w -> Domain w
union a b =
  case a of
    BVDAny _ -> a
    BVDInterval _ al aw ->
      case b of
        BVDAny _ -> b
        BVDInterval mask bl bw ->
          interval mask cl (ch - cl)
          where
            size = mask + 1
            ac = 2 * al + aw -- twice the average value of a
            bc = 2 * bl + bw -- twice the average value of b
            -- If the averages are 2^(w-1) or more apart,
            -- then shift the lower interval up by 2^w.
            al' = if ac + mask < bc then al + size else al
            bl' = if bc + mask < ac then bl + size else bl
            ah' = al' + aw
            bh' = bl' + bw
            cl = min al' bl'
            ch = max ah' bh'

-- | @concat a y@ returns domain where each element in @a@ has been
-- concatenated with an element in @y@.  The most-significant bits
-- are @a@, and the least significant bits are @y@.
concat :: NatRepr u -> Domain u -> NatRepr v -> Domain v -> Domain (u + v)
concat u a v b =
  case a of
    BVDAny _ -> BVDAny mask
    BVDInterval _ al aw -> interval mask (cat al bl) (cat aw bw)
  where
    cat i j = (i `shiftL` widthVal v) + j
    mask = maxUnsigned (addNat u v)
    (bl, bh) = ubounds b
    bw = bh - bl

-- | @shrink i a@ drops the @i@ least significant bits from @a@.
shrink ::
  NatRepr i ->
  Domain (i + n) -> Domain n
shrink i a =
  case a of
    BVDAny mask -> BVDAny (shr mask)
    BVDInterval mask al aw ->
      interval (shr mask) bl (bh - bl)
      where
        bl = shr al
        bh = shr (al + aw)
  where
    shr x = x `shiftR` widthVal i

-- | @trunc n d@ selects the @n@ least significant bits from @d@.
trunc ::
  (n <= w) =>
  NatRepr n ->
  Domain w -> Domain n
trunc n a =
  case a of
    BVDAny _ -> BVDAny mask
    BVDInterval _ al aw -> interval mask al aw
  where
    mask = maxUnsigned n

-- | @select i n a@ selects @n@ bits starting from index @i@ from @a@.
select ::
  (1 <= n, i + n <= w) =>
  NatRepr i ->
  NatRepr n ->
  Domain w -> Domain n
select i n a = shrink i (trunc (addNat i n) a)

zext :: (1 <= w, w+1 <= u) => Domain w -> NatRepr u -> Domain u
zext a u = range u al ah
  where (al, ah) = ubounds a

sext ::
  forall w u. (1 <= w, w + 1 <= u) =>
  NatRepr w ->
  Domain w ->
  NatRepr u ->
  Domain u
sext w a u =
  case fProof of
    LeqProof ->
      range u al ah
      where (al, ah) = sbounds w a
  where
    wProof :: LeqProof 1 w
    wProof = LeqProof
    uProof :: LeqProof (w+1) u
    uProof = LeqProof
    fProof :: LeqProof 1 u
    fProof = leqTrans (leqAdd wProof (knownNat :: NatRepr 1)) uProof

--------------------------------------------------------------------------------
-- Shifts

shl :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
shl w a b
  | isBVDAny a = a
  | isSingletonZero a = a
  | isSingletonZero b = a
  | otherwise = interval mask lo (hi - lo)
    where
      mask = bvdMask a
      size = mask + 1
      (bl, bh) = ubounds b
      bl' = clamp w bl
      bh' = clamp w bh
      -- compute bounds for c = 2^b
      cl = if (mask `shiftR` bl' == 0) then size else bit bl'
      ch = if (mask `shiftR` bh' == 0) then size else bit bh'
      (lo, hi) = mulRange (zbounds a) (cl, ch)

lshr :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
lshr w a b = interval mask cl (ch - cl)
  where
    mask = bvdMask a
    (al, ah) = ubounds a
    (bl, bh) = ubounds b
    cl = al `shiftR` clamp w bh
    ch = ah `shiftR` clamp w bl

ashr :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
ashr w a b = interval mask cl (ch - cl)
  where
    mask = bvdMask a
    (al, ah) = sbounds w a
    (bl, bh) = ubounds b
    cl = al `shiftR` (if al < 0 then clamp w bl else clamp w bh)
    ch = ah `shiftR` (if ah < 0 then clamp w bh else clamp w bl)

-- | Clamp the given shift amount to the word width indicated by the
--   nat repr
clamp :: NatRepr w -> Integer -> Int
clamp w x = fromInteger (min (intValue w) x)

--------------------------------------------------------------------------------
-- Arithmetic

add :: (1 <= w) => Domain w -> Domain w -> Domain w
add a b =
  case a of
    BVDAny _ -> a
    BVDInterval _ al aw ->
      case b of
        BVDAny _ -> b
        BVDInterval mask bl bw ->
          interval mask (al + bl) (aw + bw)

negate :: (1 <= w) => Domain w -> Domain w
negate a =
  case a of
    BVDAny _ -> a
    BVDInterval mask al aw -> BVDInterval mask ((-ah) .&. mask) aw
      where ah = al + aw

scale :: (1 <= w) => Integer -> Domain w -> Domain w
scale k a
  | k == 0 = BVDInterval (bvdMask a) 0 0
  | k == 1 = a
  | otherwise =
    case a of
      BVDAny _ -> a
      BVDInterval mask al aw
        | k >= 0 -> interval mask (k * al) (k * aw)
        | otherwise -> interval mask (k * ah) (k * aw)
        where ah = al + aw

mul :: (1 <= w) => Domain w -> Domain w -> Domain w
mul a b
  | isSingletonZero a = a
  | isSingletonZero b = b
  | isBVDAny a = a
  | isBVDAny b = b
  | otherwise = interval mask cl (ch - cl)
    where
      mask = bvdMask a
      (cl, ch) = mulRange (zbounds a) (zbounds b)

-- | Choose a representative integer range (positive or negative) for
-- the given bitvector domain such that the endpoints are as close to
-- zero as possible.
zbounds :: Domain w -> (Integer, Integer)
zbounds a =
  case a of
    BVDAny mask -> (0, mask)
    BVDInterval mask lo sz -> (lo', lo' + sz)
      where lo' = if 2*lo + sz > mask then lo - (mask + 1) else lo

mulRange :: (Integer, Integer) -> (Integer, Integer) -> (Integer, Integer)
mulRange (al, ah) (bl, bh) = (cl, ch)
  where
    (albl, albh) = scaleRange al (bl, bh)
    (ahbl, ahbh) = scaleRange ah (bl, bh)
    cl = min albl ahbl
    ch = max albh ahbh

scaleRange :: Integer -> (Integer, Integer) -> (Integer, Integer)
scaleRange k (lo, hi)
  | k < 0 = (k * hi, k * lo)
  | otherwise = (k * lo, k * hi)

udiv :: (1 <= w) => Domain w -> Domain w -> Domain w
udiv a b = interval mask ql (qh - ql)
  where
    mask = bvdMask a
    (al, ah) = ubounds a
    (bl, bh) = ubounds b
    ql = al `div` max 1 bh -- assume that division by 0 does not happen
    qh = ah `div` max 1 bl -- assume that division by 0 does not happen

urem :: (1 <= w) => Domain w -> Domain w -> Domain w
urem a b
  | qh == ql = interval mask rl (rh - rl)
  | otherwise = interval mask 0 (bh - 1)
  where
    mask = bvdMask a
    (al, ah) = ubounds a
    (bl, bh) = ubounds b
    (ql, rl) = al `divMod` max 1 bh -- assume that division by 0 does not happen
    (qh, rh) = ah `divMod` max 1 bl -- assume that division by 0 does not happen

-- | Pairs of nonzero integers @(lo, hi)@ such that @1\/lo <= 1\/hi@.
-- This pair represents the set of all nonzero integers @x@ such that
-- @1\/lo <= 1\/x <= 1\/hi@.
data ReciprocalRange = ReciprocalRange Integer Integer

-- | Nonzero signed values in a domain with the least and greatest
-- reciprocals.
rbounds :: (1 <= w) => NatRepr w -> Domain w -> ReciprocalRange
rbounds w a =
  case a of
    BVDAny _ -> ReciprocalRange (-1) 1
    BVDInterval mask al aw
      | ah > mask + 1 -> ReciprocalRange (-1) 1
      | otherwise     -> ReciprocalRange (signed (min mask ah)) (signed (max 1 al))
      where
        ah = al + aw
        signed x = if x < halfRange w then x else x - (mask + 1)

-- | Interval arithmetic for integer division (rounding towards 0).
-- Given @a@ and @b@ with @al <= a <= ah@ and @1\/bl <= 1\/b <= 1/bh@,
-- @sdivRange (al, ah) (ReciprocalRange bl bh)@ returns @(ql, qh)@
-- such that @ql <= a `quot` b <= qh@.
sdivRange :: (Integer, Integer) -> ReciprocalRange -> (Integer, Integer)
sdivRange (al, ah) (ReciprocalRange bl bh) = (ql, qh)
  where
    (ql1, qh1) = scaleDownRange (al, ah) bh
    (ql2, qh2) = scaleDownRange (al, ah) bl
    ql = min ql1 ql2
    qh = max qh1 qh2

-- | @scaleDownRange (lo, hi) k@ returns an interval @(ql, qh)@ such that for any
-- @x@ in @[lo..hi]@, @x `quot` k@ is in @[ql..qh]@.
scaleDownRange :: (Integer, Integer) -> Integer -> (Integer, Integer)
scaleDownRange (lo, hi) k
  | k > 0 = (lo `quot` k, hi `quot` k)
  | k < 0 = (hi `quot` k, lo `quot` k)
  | otherwise = (lo, hi) -- assume k is nonzero


sdiv :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sdiv w a b = interval mask ql (qh - ql)
  where
    mask = bvdMask a
    (ql, qh) = sdivRange (sbounds w a) (rbounds w b)

srem :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
srem w a b =
  -- If the quotient is a singleton @q@, then we compute the remainder
  -- @r = a - q*b@.
  if ql == qh then
    (if ql < 0
     then interval mask (al - ql * bl) (aw - ql * bw)
     else interval mask (al - ql * bh) (aw + ql * bw))
  -- Otherwise the range of possible remainders is determined by the
  -- modulus and the sign of the first argument.
  else interval mask rl (rh - rl)
  where
    mask = bvdMask a
    (al, ah) = sbounds w a
    (bl, bh) = sbounds w b
    (ql, qh) = sdivRange (al, ah) (rbounds w b)
    rl = if al < 0 then min (bl+1) (-bh+1) else 0
    rh = if ah > 0 then max (-bl-1) (bh-1) else 0
    aw = ah - al
    bw = bh - bl

--------------------------------------------------------------------------------
-- Bitwise logical

-- | Complement bits in range.
not :: Domain w -> Domain w
not a =
  case a of
    BVDAny _ -> a
    BVDInterval mask al aw ->
      BVDInterval mask (ah `Bits.xor` mask) aw
      where ah = al + aw

-- | Return bitwise bounds for domain (i.e. logical AND of all
-- possible values, paired with logical OR of all possible values).
bitbounds :: Domain w -> (Integer, Integer)
bitbounds a =
  case a of
    BVDAny mask -> (0, mask)
    BVDInterval mask al aw
      | al + aw > mask -> (0, mask)
      | otherwise -> (lo, hi)
      where
        au = unknowns a
        hi = al .|. au
        lo = hi `Bits.xor` au

-- | @unknowns lo hi@ returns a bitmask representing the set of bit
-- positions whose values are not constant throughout the range
-- @lo..hi@.
unknowns :: Domain w -> Integer
unknowns (BVDAny mask) = mask
unknowns (BVDInterval _mask al aw) = fillright 1 (al `Bits.xor` (al+aw))
  where
    -- @fillright 1 x@ rounds up @x@ to the nearest 2^n-1.
    fillright :: Int -> Integer -> Integer
    fillright i x
      | x' == x = x
      | otherwise = fillright (2 * i) x'
      where x' = x .|. (x `shiftR` i)

bitle :: Integer -> Integer -> Bool
bitle x y = (x .|. y) == y

------------------------------------------------------------------
-- Correctness properties

-- | Check that a domain is proper, and that
--   the given value is a member
pmember :: NatRepr n -> Domain n -> Integer -> Bool
pmember n a x = proper n a && member a x

correct_any :: (1 <= n) => NatRepr n -> Integer -> Property
correct_any w x = property (pmember w (any w) x)

correct_ubounds :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Property
correct_ubounds n (a,x) = pmember n a x' ==> lo <= x' && x' <= hi
  where
  x' = toUnsigned n x
  (lo,hi) = ubounds a

correct_sbounds :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Property
correct_sbounds n (a,x) = pmember n a x' ==> lo <= x' && x' <= hi
  where
  x' = toSigned n x
  (lo,hi) = sbounds n a

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
  (member a x || member b x) ==> pmember n (union a b) x

correct_zero_ext :: (1 <= w, w+1 <= u) => NatRepr w -> Domain w -> NatRepr u -> Integer -> Property
correct_zero_ext w a u x = member a x' ==> pmember u (zext a u) x'
  where
  x' = toUnsigned w x

correct_sign_ext :: (1 <= w, w+1 <= u) => NatRepr w -> Domain w -> NatRepr u -> Integer -> Property
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

correct_add :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_add n (a,x) (b,y) = member a x ==> member b y ==> pmember n (add a b) (x + y)

correct_neg :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Property
correct_neg n (a,x) = member a x ==> pmember n (negate a) (Prelude.negate x)

correct_not :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Property
correct_not n (a,x) = member a x ==> pmember n (not a) (complement x)

correct_mul :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_mul n (a,x) (b,y) = member a x ==> member b y ==> pmember n (mul a b) (x * y)

correct_udiv :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_udiv n (a,x) (b,y) = member a x' ==> member b y' ==> y' /= 0 ==> pmember n (udiv a b) (x' `quot` y')
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_urem :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_urem n (a,x) (b,y) = member a x' ==> member b y' ==> y' /= 0 ==> pmember n (urem a b) (x' `rem` y')
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_sdivRange :: (Integer, Integer) -> (Integer, Integer) -> Integer -> Integer -> Property
correct_sdivRange a b x y =
   mem a x ==> mem b y ==> y /= 0 ==> mem (sdivRange a b') (x `quot` y)
 where
 b' = ReciprocalRange (snd b) (fst b)
 mem (lo,hi) v = lo <= v && v <= hi

correct_sdiv :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_sdiv n (a,x) (b,y) =
    member a x ==> member b y ==> y /= 0 ==> pmember n (sdiv n a b) (x' `quot` y')
  where
  x' = toSigned n x
  y' = toSigned n y

correct_srem :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_srem n (a,x) (b,y) =
    member a x ==> member b y ==> y /= 0 ==> pmember n (srem n a b) (x' `rem` y')
  where
  x' = toSigned n x
  y' = toSigned n y

correct_shl :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_shl n (a,x) (b,y) = member a x ==> member b y ==> pmember n (shl n a b) z
  where
  z = (toUnsigned n x) `shiftL` fromInteger (min (intValue n) y)

correct_lshr :: (1 <= n) => NatRepr n ->  (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_lshr n (a,x) (b,y) = member a x ==> member b y ==> pmember n (lshr n a b) z
  where
  z = (toUnsigned n x) `shiftR` fromInteger (min (intValue n) y)

correct_ashr :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_ashr n (a,x) (b,y) = member a x ==> member b y ==> pmember n (ashr n a b) z
  where
  z = (toSigned n x) `shiftR` fromInteger (min (intValue n) y)

correct_eq :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_eq n (a,x) (b,y) =
  member a x ==> member b y ==>
    case eq a b of
      Just True  -> toUnsigned n x == toUnsigned n y
      Just False -> toUnsigned n x /= toUnsigned n y
      Nothing    -> True

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

correct_unknowns :: (1 <= n) => Domain n -> Integer -> Integer -> Property
correct_unknowns a x y = member a x ==> member a y ==> ((x .|. u) == (y .|. u)) && (u .|. mask == mask)
  where
  u = unknowns a
  mask = bvdMask a

correct_bitbounds :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Property
correct_bitbounds n (a,x) =
    member a x ==> (bitle lo x' && bitle x' hi && bitle hi (maxUnsigned n))
  where
  x' = toUnsigned n x
  (lo, hi) = bitbounds a

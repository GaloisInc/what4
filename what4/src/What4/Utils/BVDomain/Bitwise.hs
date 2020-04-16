{-|
Module      : What4.Utils.BVDomain.Bitwise
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

module What4.Utils.BVDomain.Bitwise
  ( Domain
  , bvdMask
  , member
  , asSingleton
  , nonempty
  , eq
  , domainsOverlap
  , bitbounds
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
import           Test.QuickCheck (Property, property, (==>), Gen, chooseInteger)

import qualified Prelude
import           Prelude hiding (any, concat, negate, and, or, not)

import qualified What4.Utils.Arithmetic as Arith

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
 deriving (Show)

member :: Domain w -> Integer -> Bool
member (BVBitInterval mask lo hi) x = bitle lo x' && bitle x' hi
  where x' = x .&. mask

bitle :: Integer -> Integer -> Bool
bitle x y = (x .|. y) == y

bvdMask :: Domain w -> Integer
bvdMask (BVBitInterval mask _ _) = mask

-- | Random generator for domain values.  We always generate
--   nonempty domains values.
genDomain :: NatRepr w -> Gen (Domain w)
genDomain w =
  do let mask = maxUnsigned w
     lo <- chooseInteger (0, mask)
     hi <- chooseInteger (0, mask)
     pure $! interval mask lo (lo .|. hi)

-- This generator goes to some pains to try
-- to generate a good statistical distribution
-- of the values in the domain.  It only choses
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
       stripe val' (x `shiftR` 1) (i+1)
   | otherwise = stripe val x (i+1)

{- A faster generator, but I worry that it
   doesn't have very good statistical properties...

genElement :: Domain w -> Gen Integer
genElement (BVBitInterval mask lo hi) =
  do let u = Bits.xor lo hi
     x <- chooseInteger (0, mask)
     pure ((x .&. u) .|. lo)
-}


genPair :: NatRepr w -> Gen (Domain w, Integer)
genPair w =
  do a <- genDomain w
     x <- genElement a
     return (a,x)

-- | Unsafe constructor for internal use.
interval :: Integer -> Integer -> Integer -> Domain w
interval mask lo hi = BVBitInterval mask lo hi

range :: NatRepr w -> Integer -> Integer -> Domain w
range w lo hi = BVBitInterval (maxUnsigned w) lo' hi'
  where
  lo'  = lo .&. mask
  hi'  = hi .&. mask
  mask = maxUnsigned w

bitbounds :: Domain w -> (Integer, Integer)
bitbounds (BVBitInterval _ lo hi) = (lo, hi)

-- | Test if this domain contains a single value, and return it if so
asSingleton :: Domain w -> Maybe Integer
asSingleton (BVBitInterval _ lo hi) = if lo == hi then Just lo else Nothing

-- | Returns true iff there is at least on element
--   in this bitwise domain.
nonempty :: Domain w -> Bool
nonempty (BVBitInterval _mask lo hi) = bitle lo hi

-- | Return a domain containing just the given value
singleton :: NatRepr w -> Integer -> Domain w
singleton w x = BVBitInterval mask x' x'
  where
  x' = x .&. mask
  mask = maxUnsigned w

any :: NatRepr w -> Domain w
any w = BVBitInterval mask 0 mask
  where
  mask = maxUnsigned w

-- | Returns true iff the domains have some value in common
domainsOverlap :: Domain w -> Domain w -> Bool
domainsOverlap a b = nonempty (intersection a b)

eq :: Domain w -> Domain w -> Maybe Bool
eq a b
  | Just x <- asSingleton a
  , Just y <- asSingleton b
  = Just (x == y)

  | Prelude.not (domainsOverlap a b) = Just False
  | otherwise = Nothing

intersection :: Domain w -> Domain w -> Domain w
intersection (BVBitInterval mask alo ahi) (BVBitInterval _ blo bhi) =
  BVBitInterval mask (alo .|. blo) (ahi .&. bhi)

union :: Domain w -> Domain w -> Domain w
union (BVBitInterval mask alo ahi) (BVBitInterval _ blo bhi) =
  BVBitInterval mask (alo .&. blo) (ahi .|. bhi)

-- | @concat a y@ returns domain where each element in @a@ has been
-- concatenated with an element in @y@.  The most-significant bits
-- are @a@, and the least significant bits are @y@.
concat :: NatRepr u -> Domain u -> NatRepr v -> Domain v -> Domain (u + v)
concat u (BVBitInterval _ alo ahi) v (BVBitInterval _ blo bhi) =
    BVBitInterval mask (cat alo blo) (cat ahi bhi)
  where
    cat i j = i `shiftL` widthVal v + j
    mask = maxUnsigned (addNat u v)

-- | @shrink i a@ drops the @i@ least significant bits from @a@.
shrink ::
  NatRepr i ->
  Domain (i + n) -> Domain n
shrink i (BVBitInterval mask lo hi) = BVBitInterval (shr mask) (shr lo) (shr hi)
  where
  shr x = x `shiftR` widthVal i

-- | @trunc n d@ selects the @n@ least significant bits from @d@.
trunc ::
  (n <= w) =>
  NatRepr n ->
  Domain w ->
  Domain n
trunc n (BVBitInterval _ lo hi) = range n lo hi

-- | @select i n a@ selects @n@ bits starting from index @i@ from @a@.
select ::
  (1 <= n, i + n <= w) =>
  NatRepr i ->
  NatRepr n ->
  Domain w -> Domain n
select i n a = shrink i (trunc (addNat i n) a)

zext :: (1 <= w, w+1 <= u) => Domain w -> NatRepr u -> Domain u
zext (BVBitInterval _ lo hi) u = range u lo hi

sext :: (1 <= w, w+1 <= u) => NatRepr w -> Domain w -> NatRepr u -> Domain u
sext w (BVBitInterval _ lo hi) u = range u lo' hi'
  where
  lo' = toSigned w lo
  hi' = toSigned w hi

testBit :: Domain w -> Natural -> Maybe Bool
testBit (BVBitInterval _mask lo hi) i = if lob == hib then Just lob else Nothing
  where
  lob = Bits.testBit lo j
  hib = Bits.testBit hi j
  j = fromIntegral i

shl :: NatRepr w -> Domain w -> Integer -> Domain w
shl w (BVBitInterval mask lo hi) y = BVBitInterval mask (shleft lo) (shleft hi)
  where
  y' = fromInteger (min y (intValue w))
  shleft x = (x `shiftL` y') .&. mask

rol :: NatRepr w -> Domain w -> Integer -> Domain w
rol w (BVBitInterval mask lo hi) y =
  BVBitInterval mask (Arith.rotateLeft w lo y) (Arith.rotateLeft w hi y)

ror :: NatRepr w -> Domain w -> Integer -> Domain w
ror w (BVBitInterval mask lo hi) y =
  BVBitInterval mask (Arith.rotateRight w lo y) (Arith.rotateRight w hi y)

lshr :: NatRepr w -> Domain w -> Integer -> Domain w
lshr w (BVBitInterval mask lo hi) y = BVBitInterval mask (shr lo) (shr hi)
  where
  y' = fromInteger (min y (intValue w))
  shr x = x `shiftR` y'

ashr :: (1 <= w) => NatRepr w -> Domain w -> Integer -> Domain w
ashr w (BVBitInterval mask lo hi) y = BVBitInterval mask (shr lo) (shr hi)
  where
  y' = fromInteger (min y (intValue w))
  shr x = ((toSigned w x) `shiftR` y') .&. mask

not :: Domain w -> Domain w
not (BVBitInterval mask alo ahi) =
  BVBitInterval mask (ahi `Bits.xor` mask) (alo `Bits.xor` mask)

and :: Domain w -> Domain w -> Domain w
and (BVBitInterval mask alo ahi) (BVBitInterval _ blo bhi) =
  BVBitInterval mask (alo .&. blo) (ahi .&. bhi)

or :: Domain w -> Domain w -> Domain w
or (BVBitInterval mask alo ahi) (BVBitInterval _ blo bhi) =
  BVBitInterval mask (alo .|. blo) (ahi .|. bhi)

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
-- Correctness properties

correct_any :: (1 <= n) => NatRepr n -> Integer -> Property
correct_any w x = property (member (any w) x)

correct_singleton :: (1 <= n) => NatRepr n -> Integer -> Integer -> Property
correct_singleton n x y = property (member (singleton n x') y' == (x' == y'))
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_overlap :: Domain n -> Domain n -> Integer -> Property
correct_overlap a b x =
  member a x && member b x ==> domainsOverlap a b

correct_union :: (1 <= n) => Domain n -> Domain n -> Integer -> Property
correct_union a b x =
  member a x || member b x ==> member (union a b) x

correct_intersection :: (1 <= n) => Domain n -> Domain n -> Integer -> Property
correct_intersection a b x =
  member a x && member b x ==> member (intersection a b) x

correct_zero_ext :: (1 <= w, w+1 <= u) => NatRepr w -> Domain w -> NatRepr u -> Integer -> Property
correct_zero_ext w a u x = member a x' ==> member (zext a u) x'
  where
  x' = toUnsigned w x

correct_sign_ext :: (1 <= w, w+1 <= u) => NatRepr w -> Domain w -> NatRepr u -> Integer -> Property
correct_sign_ext w a u x = member a x' ==> member (sext w a u) x'
  where
  x' = toSigned w x

correct_concat :: NatRepr m -> (Domain m,Integer) -> NatRepr n -> (Domain n,Integer) -> Property
correct_concat m (a,x) n (b,y) = member a x' ==> member b y' ==> member (concat m a n b) z
  where
  x' = toUnsigned m x
  y' = toUnsigned n y
  z  = x' `shiftL` (widthVal n) .|. y'

correct_shrink :: NatRepr i -> (Domain (i + n), Integer) -> Property
correct_shrink i (a,x) = member a x' ==> member (shrink i a) (x' `shiftR` widthVal i)
  where
  x' = x .&. bvdMask a

correct_trunc :: (n <= w) => NatRepr n -> (Domain w, Integer) -> Property
correct_trunc n (a,x) = member a x' ==> member (trunc n a) (toUnsigned n x')
  where
  x' = x .&. bvdMask a

correct_select :: (1 <= n, i + n <= w) =>
  NatRepr i -> NatRepr n -> (Domain w, Integer) -> Property
correct_select i n (a, x) = member a x ==> member (select i n a) y
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
correct_shl n (a,x) y = member a x ==> member (shl n a y) z
  where
  z = (toUnsigned n x) `shiftL` fromInteger (min (intValue n) y)

correct_lshr :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Integer -> Property
correct_lshr n (a,x) y = member a x ==> member (lshr n a y) z
  where
  z = (toUnsigned n x) `shiftR` fromInteger (min (intValue n) y)

correct_ashr :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Integer -> Property
correct_ashr n (a,x) y = member a x ==> member (ashr n a y) z
  where
  z = (toSigned n x) `shiftR` fromInteger (min (intValue n) y)

correct_rol :: (1 <= n) => NatRepr n -> (Domain n,Integer) -> Integer -> Property
correct_rol n (a,x) y = member a x ==> member (rol n a y) (Arith.rotateLeft n x y)

correct_ror :: (1 <= n) => NatRepr n -> (Domain n,Integer) -> Integer -> Property
correct_ror n (a,x) y = member a x ==> member (ror n a y) (Arith.rotateRight n x y)

correct_not :: (1 <= n) => (Domain n, Integer) -> Property
correct_not (a,x) = member a x ==> member (not a) (complement x)

correct_and :: (1 <= n) => (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_and (a,x) (b,y) = member a x ==> member b y ==> member (and a b) (x .&. y)

correct_or :: (1 <= n) => (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_or (a,x) (b,y) = member a x ==> member b y ==> member (or a b) (x .|. y)

correct_xor :: (1 <= n) => (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_xor (a,x) (b,y) = member a x ==> member b y ==> member (xor a b) (x `Bits.xor` y)

correct_testBit :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> Natural -> Property
correct_testBit n (a,x) i =
  i < natValue n ==>
    case testBit a i of
      Just True  -> Bits.testBit x (fromIntegral i)
      Just False -> Prelude.not (Bits.testBit x (fromIntegral i))
      Nothing    -> True

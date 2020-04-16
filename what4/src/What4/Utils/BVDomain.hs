{-|
Module      : What4.Utils.BVDomain
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
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module What4.Utils.BVDomain
  ( -- * Bitvector abstract domains
    BVDomain(..)
  , proper
  , member
    -- ** Domain transfer functions
  , asArithDomain
  , asBitwiseDomain
  , asXorDomain
  , fromXorDomain
  , arithToXorDomain
  , bitwiseToXorDomain
  , xorToBitwiseDomain
    -- ** Projection functions
  , asSingleton
  , eq
  , slt
  , ult
  , testBit
  , domainsOverlap
  , ubounds
  , sbounds
  , A.arithDomainData
  , B.bitbounds
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
    -- ** Shifts and rotates
  , shl
  , lshr
  , ashr
  , rol
  , ror
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
  , What4.Utils.BVDomain.not
  , and
  , or
  , xor

    -- ** Misc
  , popcnt
  , clz
  , ctz

    -- * Correctness properties
  , genDomain
  , genElement
  , genPair

  , correct_arithToBitwise
  , correct_bitwiseToArith
  , correct_bitwiseToXorDomain
  , correct_arithToXorDomain
  , correct_xorToBitwiseDomain
  , correct_asXorDomain
  , correct_fromXorDomain

  , correct_any
  , correct_ubounds
  , correct_sbounds
  , correct_singleton
  , correct_overlap
  , correct_union
  , correct_zero_ext
  , correct_sign_ext
  , correct_concat
  , correct_select
  , correct_add
  , correct_neg
  , correct_mul
  , correct_udiv
  , correct_urem
  , correct_sdiv
  , correct_srem
  , correct_shl
  , correct_lshr
  , correct_ashr
  , correct_rol
  , correct_ror
  , correct_eq
  , correct_ult
  , correct_slt
  , correct_and
  , correct_or
  , correct_not
  , correct_xor
  , correct_testBit
  , correct_popcnt
  , correct_clz
  , correct_ctz
  ) where

import qualified Data.Bits as Bits
import           Data.Bits hiding (testBit, xor)
import           Data.Parameterized.NatRepr
import           Numeric.Natural
import           GHC.TypeNats
import           GHC.Stack

import qualified Prelude
import           Prelude hiding (any, concat, negate, and, or, not)

import qualified What4.Utils.Arithmetic as Arith

import qualified What4.Utils.BVDomain.Arith as A
import qualified What4.Utils.BVDomain.Bitwise as B
import qualified What4.Utils.BVDomain.XOR as X

import           Test.QuickCheck (Property, property, (==>), Gen, arbitrary)


arithToBitwiseDomain :: A.Domain w -> B.Domain w
arithToBitwiseDomain a =
  let mask = A.bvdMask a in
  case A.arithDomainData a of
    Nothing -> B.interval mask 0 mask
    Just (alo,_) -> B.interval mask lo hi
      where
        u = A.unknowns a
        hi = alo .|. u
        lo = hi `Bits.xor` u

bitwiseToArithDomain :: B.Domain w -> A.Domain w
bitwiseToArithDomain b = A.interval mask lo ((hi - lo) .&. mask)
  where
  mask = B.bvdMask b
  (lo,hi) = B.bitbounds b

bitwiseToXorDomain :: B.Domain w -> X.Domain w
bitwiseToXorDomain b = X.interval mask lo hi
  where
  mask = B.bvdMask b
  (lo,hi) = B.bitbounds b

arithToXorDomain :: A.Domain w -> X.Domain w
arithToXorDomain a =
  let mask = A.bvdMask a in
  case A.arithDomainData a of
    Nothing -> X.BVDXor mask mask mask
    Just (alo,_) -> X.BVDXor mask hi u
      where
        u = A.unknowns a
        hi = alo .|. u

xorToBitwiseDomain :: X.Domain w -> B.Domain w
xorToBitwiseDomain x = B.interval mask lo hi
  where
  mask = X.bvdMask x
  (lo, hi) = X.bitbounds x

asXorDomain :: BVDomain w -> X.Domain w
asXorDomain (BVDArith a) = arithToXorDomain a
asXorDomain (BVDBitwise b) = bitwiseToXorDomain b

fromXorDomain :: X.Domain w -> BVDomain w
fromXorDomain x = BVDBitwise (xorToBitwiseDomain x)

asArithDomain :: BVDomain w -> A.Domain w
asArithDomain (BVDArith a)   = a
asArithDomain (BVDBitwise b) = bitwiseToArithDomain b

asBitwiseDomain :: BVDomain w -> B.Domain w
asBitwiseDomain (BVDArith a)   = arithToBitwiseDomain a
asBitwiseDomain (BVDBitwise b) = b

--------------------------------------------------------------------------------
-- BVDomain definition

-- | A value of type @'BVDomain' w@ represents a set of bitvectors of
-- width @w@. A BVDomain represents either an arithmetic interval, or
-- a bitwise interval.

data BVDomain (w :: Nat)
  = BVDArith !(A.Domain w)
  | BVDBitwise !(B.Domain w)
  deriving Show

bvdMask :: BVDomain w -> Integer
bvdMask x =
  case x of
    BVDArith a   -> A.bvdMask a
    BVDBitwise b -> B.bvdMask b

-- | Test if the domain satisfies its invariants
proper :: NatRepr w -> BVDomain w -> Bool
proper w (BVDArith a) = A.proper w a
proper w (BVDBitwise b) = B.proper w b

member :: BVDomain w -> Integer -> Bool
member (BVDArith a) x = A.member a x
member (BVDBitwise a) x = B.member a x

genDomain :: NatRepr w -> Gen (BVDomain w)
genDomain w =
  do b <- arbitrary
     if b then
       BVDArith <$> A.genDomain w
     else
       BVDBitwise <$> B.genDomain w

genElement :: BVDomain w -> Gen Integer
genElement (BVDArith a) = A.genElement a
genElement (BVDBitwise b) = B.genElement b

genPair :: NatRepr w -> Gen (BVDomain w, Integer)
genPair w =
  do a <- genDomain w
     x <- genElement a
     return (a,x)

--------------------------------------------------------------------------------
-- Projection functions

-- | Return value if this is a singleton.
asSingleton :: BVDomain w -> Maybe Integer
asSingleton (BVDArith a)   = A.asSingleton a
asSingleton (BVDBitwise b) = B.asSingleton b

-- | Return true if domains contain a common element.
domainsOverlap :: BVDomain w -> BVDomain w -> Bool
domainsOverlap (BVDBitwise a) (BVDBitwise b) = B.domainsOverlap a b
domainsOverlap (asArithDomain -> a) (asArithDomain -> b) = A.domainsOverlap a b

eq :: BVDomain w -> BVDomain w -> Maybe Bool
eq a b
  | Just x <- asSingleton a
  , Just y <- asSingleton b = Just (x == y)
  | domainsOverlap a b == False = Just False
  | otherwise = Nothing

-- | Check if all elements in one domain are less than all elements in other.
slt :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> Maybe Bool
slt w a b = A.slt w (asArithDomain a) (asArithDomain b)

-- | Check if all elements in one domain are less than all elements in other.
ult :: (1 <= w) => BVDomain w -> BVDomain w -> Maybe Bool
ult a b = A.ult (asArithDomain a) (asArithDomain b)

-- | Return @Just@ if every bitvector in the domain has the same bit
-- at the given index.
testBit ::
  NatRepr w ->
  BVDomain w ->
  Natural {- ^ Index of bit (least-significant bit has index 0) -} ->
  Maybe Bool
testBit _w a i = B.testBit (asBitwiseDomain a) i

ubounds :: BVDomain w -> (Integer, Integer)
ubounds a = A.ubounds (asArithDomain a)

sbounds :: (1 <= w) => NatRepr w -> BVDomain w -> (Integer, Integer)
sbounds w a = A.sbounds w (asArithDomain a)

--------------------------------------------------------------------------------
-- Operations

-- | Represents all values
any :: (1 <= w) => NatRepr w -> BVDomain w
any w = BVDBitwise (B.any w)

-- | Create a bitvector domain representing the integer.
singleton :: (HasCallStack, 1 <= w) => NatRepr w -> Integer -> BVDomain w
singleton w x = BVDBitwise (B.singleton w x)

-- | @range w l u@ returns domain containing all bitvectors formed
-- from the @w@ low order bits of some @i@ in @[l,u]@.  Note that per
-- @testBit@, the least significant bit has index @0@.
range :: NatRepr w -> Integer -> Integer -> BVDomain w
range w al ah = BVDArith (A.range w al ah)

-- | Create an abstract domain from an ascending list of elements.
-- The elements are assumed to be distinct.
fromAscEltList :: (1 <= w) => NatRepr w -> [Integer] -> BVDomain w
fromAscEltList w xs = BVDArith (A.fromAscEltList w xs)

-- | Return union of two domains.
union :: (1 <= w) => BVDomain w -> BVDomain w -> BVDomain w
union (BVDBitwise a) (BVDBitwise b) = BVDBitwise (B.union a b)
union (asArithDomain -> a) (asArithDomain -> b) = BVDArith (A.union a b)

-- | @concat a y@ returns domain where each element in @a@ has been
-- concatenated with an element in @y@.  The most-significant bits
-- are @a@, and the least significant bits are @y@.
concat :: NatRepr u -> BVDomain u -> NatRepr v -> BVDomain v -> BVDomain (u + v)
concat u (BVDArith a) v (BVDArith b) = BVDArith (A.concat u a v b)
concat u (asBitwiseDomain -> a) v (asBitwiseDomain -> b) = BVDBitwise (B.concat u a v b)

-- | @select i n a@ selects @n@ bits starting from index @i@ from @a@.
select ::
  (1 <= n, i + n <= w) =>
  NatRepr i ->
  NatRepr n ->
  BVDomain w -> BVDomain n
select i n (BVDArith a)   = BVDArith (A.select i n a)
select i n (BVDBitwise b) = BVDBitwise (B.select i n b)

zext :: (1 <= w, w+1 <= u) => BVDomain w -> NatRepr u -> BVDomain u
zext (BVDArith a) u   = BVDArith (A.zext a u)
zext (BVDBitwise b) u = BVDBitwise (B.zext b u)

sext ::
  forall w u. (1 <= w, w + 1 <= u) =>
  NatRepr w ->
  BVDomain w ->
  NatRepr u ->
  BVDomain u
sext w (BVDArith a) u   = BVDArith (A.sext w a u)
sext w (BVDBitwise b) u = BVDBitwise (B.sext w b u)

--------------------------------------------------------------------------------
-- Shifts

-- An arbitrary value; if we have to union together more than this many
-- bitwise shifts or rotates we'll fall back on some default instead
shiftBound :: Integer
shiftBound = 16

shl :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
shl w (BVDBitwise a) (asArithDomain -> b)
  | lo <= hi' && hi' - lo <= shiftBound =
      BVDBitwise $ foldl1 B.union [ B.shl w a y | y <- [lo .. hi'] ]
  where
  (lo, hi) = A.ubounds b
  hi' = max hi (intValue w)

shl w (asArithDomain -> a) (asArithDomain -> b) = BVDArith (A.shl w a b)


lshr :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
lshr w (BVDBitwise a) (asArithDomain -> b)
  | lo <= hi' && hi' - lo <= shiftBound =
      BVDBitwise $ foldl1 B.union [ B.lshr w a y | y <- [lo .. hi'] ]
  where
  (lo, hi) = A.ubounds b
  hi' = max hi (intValue w)

lshr w (asArithDomain -> a) (asArithDomain -> b) = BVDArith (A.lshr w a b)



ashr :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
ashr w (BVDBitwise a) (asArithDomain -> b)
  | lo <= hi' && hi' - lo <= shiftBound =
      BVDBitwise $ foldl1 B.union [ B.ashr w a y | y <- [lo .. hi'] ]
  where
  (lo, hi) = A.ubounds b
  hi' = max hi (intValue w)

ashr w (asArithDomain -> a) (asArithDomain -> b) = BVDArith (A.ashr w a b)


rol :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w

-- Special cases, rotating all 0 or all 1 bits makes no difference
rol _w a@(asSingleton -> Just x) _
  | x == 0 = a
  | x == bvdMask a = a

rol w (asBitwiseDomain -> a) (asArithDomain -> b) =
    if (lo <= hi && hi - lo <= shiftBound) then
      BVDBitwise $ foldl1 B.union [ B.rol w a y | y <- [lo .. hi] ]
    else
      any w

  where
  (lo, hi) = A.ubounds (A.urem b (A.singleton w (intValue w)))


ror :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w

-- Special cases, rotating all 0 or all 1 bits makes no difference
ror _w a@(asSingleton -> Just x) _
  | x == 0 = a
  | x == bvdMask a = a

ror w (asBitwiseDomain -> a) (asArithDomain -> b) =
    if (lo <= hi && hi - lo <= shiftBound) then
      BVDBitwise $ foldl1 B.union [ B.ror w a y | y <- [lo .. hi] ]
    else
      any w

  where
  (lo, hi) = A.ubounds (A.urem b (A.singleton w (intValue w)))

--------------------------------------------------------------------------------
-- Arithmetic

add :: (1 <= w) => BVDomain w -> BVDomain w -> BVDomain w
add a b
  | Just 0 <- asSingleton a = b
  | Just 0 <- asSingleton b = a
  | otherwise = BVDArith (A.add (asArithDomain a) (asArithDomain b))

negate :: (1 <= w) => BVDomain w -> BVDomain w
negate (asArithDomain -> a) = BVDArith (A.negate a)

scale :: (1 <= w) => Integer -> BVDomain w -> BVDomain w
scale k a
  | k == 1 = a
  | otherwise = BVDArith (A.scale k (asArithDomain a))

mul :: (1 <= w) => BVDomain w -> BVDomain w -> BVDomain w
mul a b
  | Just 1 <- asSingleton a = b
  | Just 1 <- asSingleton b = a
  | otherwise = BVDArith (A.mul (asArithDomain a) (asArithDomain b))

udiv :: (1 <= w) => BVDomain w -> BVDomain w -> BVDomain w
udiv (asArithDomain -> a) (asArithDomain -> b) = BVDArith (A.udiv a b)

urem :: (1 <= w) => BVDomain w -> BVDomain w -> BVDomain w
urem (asArithDomain -> a) (asArithDomain -> b) = BVDArith (A.urem a b)

sdiv :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
sdiv w (asArithDomain -> a) (asArithDomain -> b) = BVDArith (A.sdiv w a b)

srem :: (1 <= w) => NatRepr w -> BVDomain w -> BVDomain w -> BVDomain w
srem w (asArithDomain -> a) (asArithDomain -> b) = BVDArith (A.srem w a b)

--------------------------------------------------------------------------------
-- Bitwise logical

-- | Complement bits in range.
not :: BVDomain w -> BVDomain w
not (BVDArith a) = BVDArith (A.not a)
not (BVDBitwise b) = BVDBitwise (B.not b)

and :: BVDomain w -> BVDomain w -> BVDomain w
and a b
  | Just x <- asSingleton a, x == mask = b
  | Just x <- asSingleton b, x == mask = a
  | otherwise = BVDBitwise (B.and (asBitwiseDomain a) (asBitwiseDomain b))
 where
 mask = bvdMask a

or :: BVDomain w -> BVDomain w -> BVDomain w
or a b
  | Just 0 <- asSingleton a = b
  | Just 0 <- asSingleton b = a
  | otherwise = BVDBitwise (B.or (asBitwiseDomain a) (asBitwiseDomain b))

xor :: BVDomain w -> BVDomain w -> BVDomain w
xor a b
  | Just 0 <- asSingleton a = b
  | Just 0 <- asSingleton b = a
  | otherwise = BVDBitwise (B.xor (asBitwiseDomain a) (asBitwiseDomain b))

-------------------------------------------------------------------------------
-- Misc operations

popcnt :: NatRepr w -> BVDomain w -> BVDomain w
popcnt w (asBitwiseDomain -> b) = BVDArith (A.range w lo hi)
  where
  (bitlo, bithi) = B.bitbounds b
  lo = toInteger (Bits.popCount bitlo)
  hi = toInteger (Bits.popCount bithi)

clz :: NatRepr w -> BVDomain w -> BVDomain w
clz w (asBitwiseDomain -> b) = BVDArith (A.range w lo hi)
  where
  (bitlo, bithi) = B.bitbounds b
  lo = Arith.clz w bithi
  hi = Arith.clz w bitlo

ctz :: NatRepr w -> BVDomain w -> BVDomain w
ctz w (asBitwiseDomain -> b) = BVDArith (A.range w lo hi)
  where
  (bitlo, bithi) = B.bitbounds b
  lo = Arith.ctz w bithi
  hi = Arith.ctz w bitlo


------------------------------------------------------------------
-- Correctness properties

-- | Check that a domain is proper, and that
--   the given value is a member
pmember :: NatRepr n -> BVDomain n -> Integer -> Bool
pmember n a x = proper n a && member a x

correct_arithToBitwise :: NatRepr n -> (A.Domain n, Integer) -> Property
correct_arithToBitwise n (a,x) = A.member a x ==> B.pmember n (arithToBitwiseDomain a) x

correct_bitwiseToArith :: NatRepr n -> (B.Domain n, Integer) -> Property
correct_bitwiseToArith n (b,x) = B.member b x ==> A.pmember n (bitwiseToArithDomain b) x

correct_bitwiseToXorDomain :: NatRepr n -> (B.Domain n, Integer) -> Property
correct_bitwiseToXorDomain n (b,x) = B.member b x ==> X.pmember n (bitwiseToXorDomain b) x

correct_arithToXorDomain :: NatRepr n -> (A.Domain n, Integer) -> Property
correct_arithToXorDomain n (a,x) = A.member a x ==> X.pmember n (arithToXorDomain a) x

correct_xorToBitwiseDomain :: NatRepr n -> (X.Domain n, Integer) -> Property
correct_xorToBitwiseDomain n (a,x) = X.member a x ==> B.pmember n (xorToBitwiseDomain a) x

correct_asXorDomain :: NatRepr n -> (BVDomain n, Integer) -> Property
correct_asXorDomain n (a, x) = member a x ==> X.pmember n (asXorDomain a) x

correct_fromXorDomain :: NatRepr n -> (X.Domain n, Integer) -> Property
correct_fromXorDomain n (a, x) = X.member a x ==> pmember n (fromXorDomain a) x

correct_any :: (1 <= n) => NatRepr n -> Integer -> Property
correct_any n x = property (pmember n (any n) x)

correct_ubounds :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> Property
correct_ubounds n (a,x) = member a x' ==> lo <= x' && x' <= hi
  where
  x' = toUnsigned n x
  (lo,hi) = ubounds a

correct_sbounds :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> Property
correct_sbounds n (a,x) = member a x' ==> lo <= x' && x' <= hi
  where
  x' = toSigned n x
  (lo,hi) = sbounds n a

correct_singleton :: (1 <= n) => NatRepr n -> Integer -> Integer -> Property
correct_singleton n x y = property (member (singleton n x') y' == (x' == y'))
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_overlap :: BVDomain n -> BVDomain n -> Integer -> Property
correct_overlap a b x =
  member a x && member b x ==> domainsOverlap a b

correct_union :: (1 <= n) => NatRepr n -> BVDomain n -> BVDomain n -> Integer -> Property
correct_union n a b x =
  (member a x || member b x) ==> pmember n (union a b) x

correct_zero_ext :: (1 <= w, w+1 <= u) => NatRepr w -> BVDomain w -> NatRepr u -> Integer -> Property
correct_zero_ext w a u x = member a x' ==> pmember u (zext a u) x'
  where
  x' = toUnsigned w x

correct_sign_ext :: (1 <= w, w+1 <= u) => NatRepr w -> BVDomain w -> NatRepr u -> Integer -> Property
correct_sign_ext w a u x = member a x' ==> pmember u (sext w a u) x'
  where
  x' = toSigned w x

correct_concat :: NatRepr m -> (BVDomain m,Integer) -> NatRepr n -> (BVDomain n,Integer) -> Property
correct_concat m (a,x) n (b,y) =
    member a x ==> member b y ==> pmember (addNat m n) (concat m a n b) z
  where
  z = (x `shiftL` (widthVal n)) .|. y

correct_select :: (1 <= n, i + n <= w) =>
  NatRepr i -> NatRepr n -> (BVDomain w, Integer) -> Property
correct_select i n (a, x) = member a x ==> pmember n (select i n a) y
  where
  y = toUnsigned n ((x .&. bvdMask a) `shiftR` (widthVal i))

correct_add :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> (BVDomain n, Integer) -> Property
correct_add n (a,x) (b,y) = member a x ==> member b y ==> pmember n (add a b) (x + y)

correct_neg :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> Property
correct_neg n (a,x) = member a x ==> pmember n (negate a) (Prelude.negate x)

correct_mul :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> (BVDomain n, Integer) -> Property
correct_mul n (a,x) (b,y) = member a x ==> member b y ==> pmember n (mul a b) (x * y)

correct_udiv :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> (BVDomain n, Integer) -> Property
correct_udiv n (a,x) (b,y) = member a x' ==> member b y' ==> y' /= 0 ==> pmember n (udiv a b) (x' `quot` y')
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_urem :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> (BVDomain n, Integer) -> Property
correct_urem n (a,x) (b,y) = member a x' ==> member b y' ==> y' /= 0 ==> pmember n (urem a b) (x' `rem` y')
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_sdiv :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> (BVDomain n, Integer) -> Property
correct_sdiv n (a,x) (b,y) =
    member a x' ==> member b y' ==> y' /= 0 ==> pmember n (sdiv n a b) (x' `quot` y')
  where
  x' = toSigned n x
  y' = toSigned n y

correct_srem :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> (BVDomain n, Integer) -> Property
correct_srem n (a,x) (b,y) =
    member a x' ==> member b y' ==> y' /= 0 ==> pmember n (srem n a b) (x' `rem` y')
  where
  x' = toSigned n x
  y' = toSigned n y

correct_shl :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> (BVDomain n, Integer) -> Property
correct_shl n (a,x) (b,y) = member a x ==> member b y ==> pmember n (shl n a b) z
  where
  z = (toUnsigned n x) `shiftL` fromInteger (min (intValue n) y)

correct_lshr :: (1 <= n) => NatRepr n ->  (BVDomain n, Integer) -> (BVDomain n, Integer) -> Property
correct_lshr n (a,x) (b,y) = member a x ==> member b y ==> pmember n (lshr n a b) z
  where
  z = (toUnsigned n x) `shiftR` fromInteger (min (intValue n) y)

correct_ashr :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> (BVDomain n, Integer) -> Property
correct_ashr n (a,x) (b,y) = member a x ==> member b y ==> pmember n (ashr n a b) z
  where
  z = (toSigned n x) `shiftR` fromInteger (min (intValue n) y)

correct_rol :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> (BVDomain n, Integer) -> Property
correct_rol n (a,x) (b,y) = member a x ==> member b y ==> pmember n (rol n a b) (Arith.rotateLeft n x y)

correct_ror :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> (BVDomain n, Integer) -> Property
correct_ror n (a,x) (b,y) = member a x ==> member b y ==> pmember n (ror n a b) (Arith.rotateRight n x y)

correct_eq :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> (BVDomain n, Integer) -> Property
correct_eq n (a,x) (b,y) =
  member a x ==> member b y ==>
    case eq a b of
      Just True  -> toUnsigned n x == toUnsigned n y
      Just False -> toUnsigned n x /= toUnsigned n y
      Nothing    -> True

correct_ult :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> (BVDomain n, Integer) -> Property
correct_ult n (a,x) (b,y) =
  member a x ==> member b y ==>
    case ult a b of
      Just True  -> toUnsigned n x < toUnsigned n y
      Just False -> toUnsigned n x >= toUnsigned n y
      Nothing    -> True

correct_slt :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> (BVDomain n, Integer) -> Property
correct_slt n (a,x) (b,y) =
  member a x ==> member b y ==>
    case slt n a b of
      Just True  -> toSigned n x < toSigned n y
      Just False -> toSigned n x >= toSigned n y
      Nothing    -> True

correct_not :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> Property
correct_not n (a,x) = member a x ==> pmember n (not a) (complement x)

correct_and :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> (BVDomain n, Integer) -> Property
correct_and n (a,x) (b,y) = member a x ==> member b y ==> pmember n (and a b) (x .&. y)

correct_or :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> (BVDomain n, Integer) -> Property
correct_or n (a,x) (b,y) = member a x ==> member b y ==> pmember n (or a b) (x .|. y)

correct_xor :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> (BVDomain n, Integer) -> Property
correct_xor n (a,x) (b,y) = member a x ==> member b y ==> pmember n (xor a b) (x `Bits.xor` y)

correct_testBit :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> Natural -> Property
correct_testBit n (a,x) i =
  i < natValue n ==>
    case testBit n a i of
      Just True  -> Bits.testBit x (fromIntegral i)
      Just False -> Prelude.not (Bits.testBit x (fromIntegral i))
      Nothing    -> True

correct_popcnt :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> Property
correct_popcnt n (a,x) = member a x ==> pmember n (popcnt n a) (toInteger (Bits.popCount x))

correct_ctz :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> Property
correct_ctz n (a,x) = member a x ==> pmember n (ctz n a) (Arith.ctz n x)

correct_clz :: (1 <= n) => NatRepr n -> (BVDomain n, Integer) -> Property
correct_clz n (a,x) = member a x ==> pmember n (clz n a) (Arith.clz n x)


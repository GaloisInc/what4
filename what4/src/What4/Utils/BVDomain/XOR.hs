{-|
Module      : What4.Utils.BVDomain.XOR
Copyright   : (c) Galois Inc, 2019
License     : BSD3
Maintainer  : huffman@galois.com

Provides an implementation of bitvecotr abstract domains
optimized for performing XOR operations.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module What4.Utils.BVDomain.XOR
  ( -- * XOR Domains
    Domain(..)
  , proper
  , bvdMask
  , member
  , pmember
  , range
  , interval
  , bitbounds
  , asSingleton
    -- ** Operations
  , singleton
  , xor
  , and
  , and_scalar

    -- * Correctness properties
  , genDomain
  , genElement
  , genPair

  , correct_singleton
  , correct_xor
  , correct_and
  , correct_and_scalar
  , correct_bitbounds
  ) where


import qualified Data.Bits as Bits
import           Data.Bits hiding (testBit, xor)
import           Data.Parameterized.NatRepr
import           GHC.TypeNats

import           Prelude hiding (any, concat, negate, and, or, not)

import           Test.Verification ( Property, property, (==>), Gen, chooseInteger )

-- | A value of type @'BVDomain' w@ represents a set of bitvectors of
-- width @w@.  This is an alternate representation of the bitwise
-- domain values, optimized to compute XOR operations.
data Domain (w :: Nat) =
    BVDXor !Integer !Integer !Integer
    -- ^ @BVDXor mask hi unknown@ represents a set of values where
    --   @hi@ is a bitwise high bound, and @unknown@ represents
    --   the bits whose values are not known.  The value @mask@
    --   caches the value @2^w-1@.
  deriving (Show)

-- | Test if the domain satisfies its invariants
proper :: NatRepr w -> Domain w -> Bool
proper w (BVDXor mask val u) =
  mask == maxUnsigned w &&
  bitle val mask &&
  bitle u mask &&
  bitle u val

member :: Domain w -> Integer -> Bool
member (BVDXor mask hi unknown) x = hi == (x .&. mask) .|. unknown

bvdMask :: Domain w -> Integer
bvdMask (BVDXor mask _ _) = mask

range :: NatRepr w -> Integer -> Integer -> Domain w
range w lo hi = interval mask lo' hi'
  where
  lo'  = lo .&. mask
  hi'  = hi .&. mask
  mask = maxUnsigned w

-- | Unsafe constructor for internal use.
interval :: Integer -> Integer -> Integer -> Domain w
interval mask lo hi = BVDXor mask hi (Bits.xor lo hi)

bitbounds :: Domain w -> (Integer, Integer)
bitbounds (BVDXor _ hi u) = (Bits.xor u hi, hi)

-- | Test if this domain contains a single value, and return it if so
asSingleton :: Domain w -> Maybe Integer
asSingleton (BVDXor _ hi u) = if u == 0 then Just hi else Nothing

genDomain :: NatRepr w -> Gen (Domain w)
genDomain w =
  do let mask = maxUnsigned w
     val <- chooseInteger (0, mask)
     u   <- chooseInteger (0, mask)
     pure $ BVDXor mask (val .|. u) u

genElement :: Domain w -> Gen Integer
genElement (BVDXor _mask v u) =
   do x <- chooseInteger (0, bit bs - 1)
      pure $ stripe lo x 0

  where
  lo = v `Bits.xor` u
  bs = Bits.popCount u
  stripe val x i
   | x == 0 = val
   | Bits.testBit u i =
       let val' = if Bits.testBit x 0 then setBit val i else val in
       stripe val' (x `shiftR` 1) (i+1)
   | otherwise = stripe val x (i+1)

genPair :: NatRepr w -> Gen (Domain w, Integer)
genPair w =
  do a <- genDomain w
     x <- genElement a
     pure (a,x)


singleton :: NatRepr w -> Integer -> Domain w
singleton w x = BVDXor mask (x .&. mask) 0
  where
  mask = maxUnsigned w

xor :: Domain w -> Domain w -> Domain w
xor (BVDXor mask va ua) (BVDXor _ vb ub) = BVDXor mask (v .|. u) u
  where
  v = Bits.xor va vb
  u = ua .|. ub

and :: Domain w -> Domain w -> Domain w
and (BVDXor mask va ua) (BVDXor _ vb ub) = BVDXor mask v (v .&. u)
  where
  v = va .&. vb
  u = ua .|. ub

and_scalar :: Integer -> Domain w -> Domain w
and_scalar x (BVDXor mask va ua) = BVDXor mask (va .&. x) (ua .&. x)

-----------------------------------------------------------------------
-- Correctness properties

-- | Check that a domain is proper, and that
--   the given value is a member
pmember :: NatRepr n -> Domain n -> Integer -> Bool
pmember n a x = proper n a && member a x

correct_singleton :: (1 <= n) => NatRepr n -> Integer -> Integer -> Property
correct_singleton n x y = property (pmember n (singleton n x') y' == (x' == y'))
  where
  x' = toUnsigned n x
  y' = toUnsigned n y

correct_xor :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_xor n (a,x) (b,y) = member a x ==> member b y ==> pmember n (xor a b) (x `Bits.xor` y)

correct_and :: (1 <= n) => NatRepr n -> (Domain n, Integer) -> (Domain n, Integer) -> Property
correct_and n (a,x) (b,y) = member a x ==> member b y ==> pmember n (and a b) (x .&. y)

correct_and_scalar :: (1 <= n) => NatRepr n -> Integer -> (Domain n, Integer) -> Property
correct_and_scalar n y (a,x) = member a x ==> pmember n (and_scalar y a) (y .&. x)

bitle :: Integer -> Integer -> Bool
bitle x y = (x .|. y) == y

correct_bitbounds :: Domain n -> Integer -> Property
correct_bitbounds a x = property (member a x == (bitle lo x && bitle x hi))
  where
  (lo,hi) = bitbounds a

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}

-- | Internal module exposing both optimized and reference implementations
-- for property testing. Items in this module should /not/ be considered part
-- of What4's API; they are exported only for the sake of the test suite.
module What4.Domains.Arithmetic.Internal
  ( -- * Reference implementations (always available)
    ctzRef
  , clzRef
  , intLog2Ref
    -- * Optimized implementations (GHC 9.0+ only)
  , ctzOpt
  , clzOpt
  , intLog2Opt
  ) where

import Data.Bits (Bits(..), testBit, shiftR)

import Data.Parameterized.NatRepr

#if MIN_VERSION_base(4,15,0)
import qualified GHC.Num.Integer as Integer
import qualified GHC.Num.BigNat as BigNat
import GHC.Exts (Word(..), ctz#, int2Word#)
#endif

------------------------------------------------------------------------
-- Reference implementations (naive loop-based)

-- | Reference implementation: Count trailing zeros using bit testing loop
ctzRef :: NatRepr w -> Integer -> Integer
ctzRef w x = go 0
 where
 go !i
   | i < toInteger (natValue w) && testBit x (fromInteger i) == False = go (i + 1)
   | otherwise = i
{-# INLINABLE ctzRef #-}

-- | Reference implementation: Count leading zeros using bit testing loop
clzRef :: NatRepr w -> Integer -> Integer
clzRef w x = go 0
 where
 go !i
   | i < toInteger (natValue w) && testBit x (widthVal w - fromInteger i - 1) == False = go (i + 1)
   | otherwise = i
{-# INLINABLE clzRef #-}

-- | Reference implementation: Floor of log base 2 using shift loop
intLog2Ref :: Integer -> Int
intLog2Ref = go 0
  where
  go !k m
    | m <= 1    = k
    | otherwise = go (k + 1) (m `shiftR` 1)
{-# INLINABLE intLog2Ref #-}

------------------------------------------------------------------------
-- Optimized implementations (GHC 9.0+ primops)

-- | Optimized implementation: Count trailing zeros using ghc-bignum primops
ctzOpt :: NatRepr w -> Integer -> Integer
#if MIN_VERSION_base(4,15,0)
ctzOpt w x
  | x == 0 = toInteger (natValue w)
  | otherwise =
      case x of
        Integer.IS i# -> min (toInteger (natValue w)) (fromIntegral $ W# (ctz# (int2Word# i#)))
        Integer.IN bn -> min (toInteger (natValue w)) (fromIntegral $ BigNat.bigNatCtz bn)
        Integer.IP bn -> min (toInteger (natValue w)) (fromIntegral $ BigNat.bigNatCtz bn)
#else
ctzOpt = ctzRef
#endif
{-# INLINE ctzOpt #-}

-- | Optimized implementation: Count leading zeros using integerLog2 primop
clzOpt :: NatRepr w -> Integer -> Integer
#if MIN_VERSION_base(4,15,0)
clzOpt w x
  | x == 0 = toInteger (natValue w)
  | otherwise =
      -- Mask to width-w value to handle negative numbers and values outside range
      let width = toInteger (natValue w)
          mask = (1 `shiftL` fromIntegral width) - 1
          x' = x .&. mask
      in if x' == 0
         then width
         else let highBit = fromIntegral (Integer.integerLog2 x')
              in if highBit >= width
                 then 0
                 else width - 1 - highBit
#else
clzOpt = clzRef
#endif
{-# INLINE clzOpt #-}

-- | Optimized implementation: Floor of log base 2 using integerLog2 primop
intLog2Opt :: Integer -> Int
#if MIN_VERSION_base(4,15,0)
intLog2Opt n = fromIntegral (Integer.integerLog2 n)
#else
intLog2Opt = intLog2Ref
#endif
{-# INLINE intLog2Opt #-}

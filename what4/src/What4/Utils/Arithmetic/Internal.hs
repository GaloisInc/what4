{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedSums #-}

-- | Internal module re-exporting arithmetic implementations from
-- What4.Domains.Arithmetic.Internal. Items in this module should /not/ be
-- considered part of What4's API; they are exported only for the sake of
-- the test suite.
--
-- Note: What4.Utils.Arithmetic delegates to What4.Domains.Arithmetic.Internal
-- to avoid code duplication.
module What4.Utils.Arithmetic.Internal
  ( -- * Reference implementations (always available)
    ctzRef
  , clzRef
  , intLog2Ref
  , isPow2IntegerRef
    -- * Optimized implementations (GHC 9.0+ only)
  , ctzOpt
  , clzOpt
  , intLog2Opt
  , isPow2IntegerOpt
  ) where

import Data.Bits (Bits(..))

#if MIN_VERSION_base(4,15,0)
import qualified GHC.Num.Integer as Integer
#endif

import What4.Domains.Arithmetic.Internal
  ( ctzRef, clzRef, intLog2Ref, ctzOpt, clzOpt, intLog2Opt )

------------------------------------------------------------------------
-- Functions unique to What4.Utils.Arithmetic

-- | Reference implementation: Check if Integer is power of two
isPow2IntegerRef :: Integer -> Bool
isPow2IntegerRef x = x .&. (x-1) == 0
{-# INLINE isPow2IntegerRef #-}

-- | Optimized implementation: Check if Integer is power of two using primops
isPow2IntegerOpt :: Integer -> Bool
#if MIN_VERSION_base(4,15,0)
isPow2IntegerOpt x = case Integer.integerIsPowerOf2# x of
  (# _ | #) -> False
  (# | _ #) -> True
#else
isPow2IntegerOpt = isPow2IntegerRef
#endif
{-# INLINE isPow2IntegerOpt #-}

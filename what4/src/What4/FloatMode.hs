-----------------------------------------------------------------------
-- |
-- Module           : What4.FloatMode
-- Description      : Mode values for controlling the "interpreted" floating point mode.
-- Copyright        : (c) Galois, Inc 2014-2022
-- License          : BSD3
-- Maintainer       : rdockins@galois.com
-- Stability        : provisional
--
-- Desired instances for the @IsInterpretedFloatExprBuilder@ class are selected
-- via the different mode values from this module.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module What4.FloatMode
  ( type FloatMode
  , FloatModeRepr(..)
  , FloatIEEE
  , FloatUninterpreted
  , FloatReal
  ) where

import           Data.Kind (Type)
import           Data.Parameterized.Classes


-- | Mode flag for how floating-point values should be interpreted.
data FloatMode where
  FloatIEEE :: FloatMode
  FloatUninterpreted :: FloatMode
  FloatReal :: FloatMode

-- | In this mode "interpreted" floating-point values are treated
--   as bit-precise IEEE-754 floats.
type FloatIEEE = 'FloatIEEE

-- | In this mode "interpreted" floating-point values are treated
--   as bitvectors of the appropriate width, and all operations on
--   them are translated as uninterpreted functions.
type FloatUninterpreted = 'FloatUninterpreted

-- | In this mode "interpreted" floating-point values are treated
--   as real-number values, to the extent possible. Expressions that
--   would result in infinities or NaN will yield unspecified values in
--   this mode, or directly produce runtime errors.
type FloatReal = 'FloatReal

data FloatModeRepr :: FloatMode -> Type where
  FloatIEEERepr          :: FloatModeRepr FloatIEEE
  FloatUninterpretedRepr :: FloatModeRepr FloatUninterpreted
  FloatRealRepr          :: FloatModeRepr FloatReal

instance Show (FloatModeRepr fm) where
  showsPrec _ FloatIEEERepr          = showString "FloatIEEE"
  showsPrec _ FloatUninterpretedRepr = showString "FloatUninterpreted"
  showsPrec _ FloatRealRepr          = showString "FloatReal"

instance ShowF FloatModeRepr

instance KnownRepr FloatModeRepr FloatIEEE          where knownRepr = FloatIEEERepr
instance KnownRepr FloatModeRepr FloatUninterpreted where knownRepr = FloatUninterpretedRepr
instance KnownRepr FloatModeRepr FloatReal          where knownRepr = FloatRealRepr

instance TestEquality FloatModeRepr where
  testEquality FloatIEEERepr           FloatIEEERepr           = return Refl
  testEquality FloatUninterpretedRepr  FloatUninterpretedRepr  = return Refl
  testEquality FloatRealRepr           FloatRealRepr           = return Refl
  testEquality _ _ = Nothing

-----------------------------------------------------------------------
-- |
-- Module           : What4.FloatMode
-- Description      : 
-- Copyright        : (c) Galois, Inc 2014-2022
-- License          : BSD3
-- Maintainer       : rdockins@galois.com
-- Stability        : provisional
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
type FloatIEEE = 'FloatIEEE
type FloatUninterpreted = 'FloatUninterpreted
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

{-|
Module           : What4.Utils.OnlyIntRepr
Copyright        : (c) Galois, Inc. 2020
License          : BSD3
Maintainer       : Joe Hendrix <jhendrix@galois.com>

Defines a GADT for indicating a base type must be an integer.  Used for
restricting index types in MATLAB arrays.
-}
{-# LANGUAGE GADTs #-}
module What4.Utils.OnlyIntRepr
  ( OnlyIntRepr(..)
  , toBaseTypeRepr
  ) where

import Data.Hashable (Hashable(..))
import Data.Parameterized.Classes (HashableF(..))
import What4.BaseTypes

-- | This provides a GADT instance used to indicate a 'BaseType' must have
-- value 'BaseIntegerType'.
data OnlyIntRepr tp
   = (tp ~ BaseIntegerType) => OnlyIntRepr

instance TestEquality OnlyIntRepr where
  testEquality OnlyIntRepr OnlyIntRepr = Just Refl

instance Eq (OnlyIntRepr tp) where
  OnlyIntRepr == OnlyIntRepr = True

instance Hashable (OnlyIntRepr tp) where
  hashWithSalt s OnlyIntRepr = s

instance HashableF OnlyIntRepr where
  hashWithSaltF = hashWithSalt

toBaseTypeRepr :: OnlyIntRepr tp -> BaseTypeRepr tp
toBaseTypeRepr OnlyIntRepr = BaseIntegerRepr

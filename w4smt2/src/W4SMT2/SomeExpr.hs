{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

-- | @newtype@-based existential quantification a la @some@ package.
--
-- One less pointer indirection than 'Data.Parameterized.Some.Some'.
module W4SMT2.SomeExpr
  ( SomeExpr(SomeExpr)
  ) where

import GHC.Exts (Any)
import Unsafe.Coerce (unsafeCoerce)

import What4.Interface (SymExpr)

newtype SomeExpr sym = UnsafeSome (SymExpr sym Any)

{-# COMPLETE SomeExpr #-}
pattern SomeExpr :: forall sym a. SymExpr sym a -> SomeExpr sym
pattern SomeExpr x <- UnsafeSome ((unsafeCoerce :: SymExpr sym Any -> SymExpr sym a) -> x)
  where SomeExpr x = UnsafeSome ((unsafeCoerce :: SymExpr sym a -> SymExpr sym Any) x)

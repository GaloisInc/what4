{-|
Module      : Who2.Unsupported
Description : Exception type for unsupported operations
Copyright   : (c) Galois, Inc 2026
License     : BSD3
Maintainer  : langston@galois.com
-}

module Who2.Unsupported
  ( Unsupported(..)
  , unsupported
  ) where

import Control.Exception (Exception, throw)

-- | Exception thrown when an unsupported operation is called.
--
-- The 'String' parameter should contain the fully qualified function name
-- (e.g., "Who2.Builder.floatAdd", "Who2.Expr.SymExpr.integerBounds").
newtype Unsupported = Unsupported String
  deriving (Eq)

instance Show Unsupported where
  show (Unsupported fnName) =
    unlines
      [ "Unsupported operation in Who2:"
      , "  " ++ fnName
      , ""
      , "Please report this issue or check for updates at:"
      , "  https://github.com/GaloisInc/what4/issues"
      ]

instance Exception Unsupported

-- | Throw an 'Unsupported' exception with the given function name.
--
-- Example usage:
--
-- @
-- integerBounds = unsupported "Who2.Expr.SymExpr.integerBounds"
-- @
unsupported :: String -> a
unsupported = throw . Unsupported

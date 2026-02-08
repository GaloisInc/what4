{-# LANGUAGE RankNTypes #-}

-- | Expression allocators for 'Who2.Builder.Builder'.
--
-- Currently, only a simple non-hash-consing allocator is implemented.
module Who2.Builder.Allocator
  ( ExprAllocator(ExprAllocator, riskyAllocExpr)
  , simpleAllocator
  ) where

import Data.Parameterized.Nonce (NonceGenerator)

import What4.Utils.AbstractDomains (AbstractValue)

import Who2.Expr.App (App)
import Who2.Expr (Expr)
import qualified Who2.Expr as Who2E

-- | Expression allocator for 'Who2.Builder.Builder'.
newtype ExprAllocator t
  = ExprAllocator
    { riskyAllocExpr ::
        forall tp.
        App t (Expr t (App t)) tp ->
        AbstractValue tp ->
        IO (Expr t (App t) tp)
    }

-- | Create a new allocator that does not do hash consing.
simpleAllocator :: NonceGenerator IO t -> ExprAllocator t
simpleAllocator g = ExprAllocator { riskyAllocExpr = Who2E.mkExpr g }
{-# INLINE simpleAllocator #-}

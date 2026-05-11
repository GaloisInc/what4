{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Who2.Expr.SymFn
  ( SymFnInfo(..)
  , SymFn(..)
  , UnfoldPolicy(..)
  , symFnArgTypes
  , symFnReturnType
  , testSymFnEq
  , compareSymFn
  , hashSymFn
  ) where

import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Ctx (type (::>))
import           Data.Parameterized.Nonce (Nonce)
import           Data.Parameterized.TraversableFC (fmapFC)

import qualified What4.BaseTypes as BT
import qualified What4.Expr as WE
import qualified What4.Expr.App as WEA
import qualified What4.Interface as WI
import qualified What4.ProgramLoc as WPL
import qualified What4.Symbol as WS

import Data.Kind (Type)

-- | Policy for when to unfold (inline) a defined function
data UnfoldPolicy = AlwaysUnfold
  deriving (Eq, Ord, Show)

-- | Information about a symbolic function
-- This is extensible via GADT to support future function kinds
-- The @f@ parameter is the expression type to avoid circular dependencies
data SymFnInfo t (f :: BT.BaseType -> Type) (args :: Ctx.Ctx BT.BaseType) (ret :: BT.BaseType) where
  -- | An uninterpreted function with only a signature (no body)
  UninterpFnInfo ::
    !(Ctx.Assignment BT.BaseTypeRepr args) ->
    !(BT.BaseTypeRepr ret) ->
    SymFnInfo t f args ret

  -- | A defined function with an explicit body that can be inlined
  DefinedFnInfo ::
    !(Ctx.Assignment (WE.ExprBoundVar t) args) ->  -- Formal parameters
    !(f ret) ->                                     -- Function body
    !UnfoldPolicy ->                                -- When to inline
    !(BT.BaseTypeRepr ret) ->                       -- Return type (cached)
    SymFnInfo t f args ret
  -- Future extension point: MatlabSolverFnInfo

-- | A symbolic function with a unique identifier
data SymFn t (f :: BT.BaseType -> Type) (args :: Ctx.Ctx BT.BaseType) (ret :: BT.BaseType)
  = SymFn
    { symFnId :: !(Nonce t (args ::> ret))
    , symFnName :: !WS.SolverSymbol
    , symFnInfo :: !(SymFnInfo t f args ret)
    , symFnLoc :: !WPL.ProgramLoc
    }

-- | Extract the argument types from a symbolic function
symFnArgTypes :: SymFn t f args ret -> Ctx.Assignment BT.BaseTypeRepr args
symFnArgTypes fn = case symFnInfo fn of
  UninterpFnInfo args _ -> args
  DefinedFnInfo vars _ _ _ -> fmapFC WEA.bvarType vars

-- | Extract the return type from a symbolic function
symFnReturnType :: SymFn t f args ret -> BT.BaseTypeRepr ret
symFnReturnType fn = case symFnInfo fn of
  UninterpFnInfo _ ret -> ret
  DefinedFnInfo _ _ _ ret -> ret

-- | Show instance for debugging
instance Show (SymFn t f args ret) where
  show fn = "SymFn{" ++ show (symFnName fn) ++ "}"

-- | Test equality of two symbolic functions
-- Returns proof that the combined argument+return types are equal
testSymFnEq ::
  SymFn t f args1 ret1 ->
  SymFn t f args2 ret2 ->
  Maybe ((args1 ::> ret1) PC.:~: (args2 ::> ret2))
testSymFnEq fn1 fn2 = PC.testEquality (symFnId fn1) (symFnId fn2)

-- | Compare two symbolic functions by nonce
compareSymFn ::
  SymFn t f args1 ret1 ->
  SymFn t f args2 ret2 ->
  PC.OrderingF (args1 ::> ret1) (args2 ::> ret2)
compareSymFn fn1 fn2 = PC.compareF (symFnId fn1) (symFnId fn2)

-- | Hash a symbolic function by its nonce
hashSymFn :: Int -> SymFn t f args ret -> Int
hashSymFn salt fn = PC.hashWithSalt salt (symFnId fn)

-- | IsSymFn instance for Who2 SymFn
instance WI.IsSymFn (SymFn t f) where
  fnArgTypes = symFnArgTypes
  fnReturnType = symFnReturnType
  fnTestEquality = testSymFnEq
  fnCompare = compareSymFn


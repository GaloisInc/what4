{-|
Module      : What4.Expr
Description : Commonly-used reexports from the expression representation
Copyright   : (c) Galois, Inc 2015-2020
License     : BSD3
Maintainer  : Rob Dockins <rdockins@galois.com>

The module reexports the most commonly used types
and operations of the What4 expression representation.
-}

module What4.Expr
  ( -- * Expression builder
    ExprBuilder
  , newExprBuilder
  , startCaching
  , stopCaching
  , userState
  , exprCounter
  , curProgramLoc
  , unaryThreshold
  , cacheStartSize
  , pushMuxOps
  , exprBuilderSplitConfig
  , exprBuilderFreshConfig
  , EmptyExprBuilderState(..)

    -- * Flags
  , FloatMode
  , FloatModeRepr(..)
  , FloatIEEE
  , FloatUninterpreted
  , FloatReal
  , Flags

    -- * Type abbreviations
  , BoolExpr
  , IntegerExpr
  , RealExpr
  , BVExpr
  , CplxExpr
  , StringExpr

    -- * Expression datatypes
  , Expr(..)
  , exprLoc
  , ppExpr

   -- ** App expressions
  , AppExpr
  , appExprId
  , appExprLoc
  , appExprApp
  , App(..)

    -- ** NonceApp expressions
  , NonceAppExpr
  , nonceExprId
  , nonceExprLoc
  , nonceExprApp
  , NonceApp(..)

    -- ** Bound variables
  , ExprBoundVar
  , bvarId
  , bvarLoc
  , bvarName
  , bvarKind
  , VarKind(..)
  , boundVars

    -- ** Symbolic functions
  , ExprSymFn(..)
  , SymFnInfo(..)
  , symFnArgTypes
  , symFnReturnType

    -- ** Semirings
  , SR.Coefficient
  , SR.SemiRing
  , SR.BVFlavor
  , SR.SemiRingRepr(..)
  , SR.BVFlavorRepr(..)
  , SR.OrderedSemiRingRepr(..)
  , WeightedSum

    -- ** Unary BV
  , UnaryBV

    -- * Logic theories
  , AppTheory(..)
  , quantTheory
  , appTheory

    -- * Ground evaluation
  , GroundValue
  , GroundValueWrapper(..)
  , GroundArray(..)
  , lookupArray
  , GroundEvalFn(..)
  , ExprRangeBindings

  ) where

import qualified What4.SemiRing as SR
import What4.Expr.AppTheory
import What4.Expr.Builder
import What4.Expr.GroundEval
import What4.Expr.WeightedSum
import What4.Expr.UnaryBV


-- | A \"dummy\" data type that can be used for the
--   user state field of an 'ExprBuilder' when there
--   is no other interesting state to track.
data EmptyExprBuilderState t = EmptyExprBuilderState

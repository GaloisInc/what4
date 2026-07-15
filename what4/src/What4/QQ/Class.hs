-----------------------------------------------------------------------
-- |
-- Module           : What4.QQ.Class
-- Description      : Sort-indexed classes for the What4 quasiquoter
-- Copyright        : (c) Galois, Inc 2026
-- License          : BSD3
-- Maintainer       : Langston Barrett <langston@galois.com>
-- Stability        : provisional
--
-- These classes let the "What4.QQ" quasiquoter resolve its overloaded
-- numeric, comparison, and logical operators at compile time, dispatching
-- on the operands' 'BaseType'.
--
-- There is intentionally /no/ implicit coercion between 'BaseIntegerType'
-- and 'BaseRealType': the operands of an overloaded operator must already
-- share a base type, or GHC reports a type error at the use site. Write an
-- explicit conversion (e.g. via 'What4.Interface.integerToReal') if you
-- need to mix them.
-----------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module What4.QQ.Class
  ( NumSort(..)
  , AbsSort(..)
  , OrdSort(..)
  , DivSort(..)
  , LogicSort(..)
  ) where

import What4.BaseTypes (BaseType, BaseBoolType, BaseBVType, BaseIntegerType, BaseRealType)
import What4.Interface (IsExprBuilder, Pred, SymExpr)
import qualified What4.Interface as WI
import GHC.TypeNats (type (<=))

-- | Numeric operations shared by integers, reals, and bitvectors.
class NumSort (tp :: BaseType) where
  sortAdd :: IsExprBuilder sym => sym -> SymExpr sym tp -> SymExpr sym tp -> IO (SymExpr sym tp)
  sortSub :: IsExprBuilder sym => sym -> SymExpr sym tp -> SymExpr sym tp -> IO (SymExpr sym tp)
  sortMul :: IsExprBuilder sym => sym -> SymExpr sym tp -> SymExpr sym tp -> IO (SymExpr sym tp)
  sortNeg :: IsExprBuilder sym => sym -> SymExpr sym tp -> IO (SymExpr sym tp)

instance NumSort BaseIntegerType where
  sortAdd = WI.intAdd
  sortSub = WI.intSub
  sortMul = WI.intMul
  sortNeg = WI.intNeg

instance NumSort BaseRealType where
  sortAdd = WI.realAdd
  sortSub = WI.realSub
  sortMul = WI.realMul
  sortNeg = WI.realNeg

instance (1 <= w) => NumSort (BaseBVType w) where
  sortAdd = WI.bvAdd
  sortSub = WI.bvSub
  sortMul = WI.bvMul
  sortNeg = WI.bvNeg

-- | Absolute value is defined for integers and reals.
class AbsSort (tp :: BaseType) where
  sortAbs :: IsExprBuilder sym => sym -> SymExpr sym tp -> IO (SymExpr sym tp)

instance AbsSort BaseIntegerType where
  sortAbs = WI.intAbs

instance AbsSort BaseRealType where
  sortAbs = WI.realAbs

-- | Ordered comparisons shared by integers and reals. @gt@ and @ge@ are
-- handled by the quasiquoter as flipped 'sortLt' / 'sortLe'.
class OrdSort (tp :: BaseType) where
  sortLt :: IsExprBuilder sym => sym -> SymExpr sym tp -> SymExpr sym tp -> IO (Pred sym)
  sortLe :: IsExprBuilder sym => sym -> SymExpr sym tp -> SymExpr sym tp -> IO (Pred sym)

instance OrdSort BaseIntegerType where
  sortLt = WI.intLt
  sortLe = WI.intLe

instance OrdSort BaseRealType where
  sortLt = WI.realLt
  sortLe = WI.realLe

-- | Division is shared by integers and reals, but not bitvectors: bitvector
-- division is explicitly signed or unsigned in the quasiquoter language.
class DivSort (tp :: BaseType) where
  sortDiv :: IsExprBuilder sym => sym -> SymExpr sym tp -> SymExpr sym tp -> IO (SymExpr sym tp)

instance DivSort BaseIntegerType where
  sortDiv = WI.intDiv

instance DivSort BaseRealType where
  sortDiv = WI.realDiv

-- | Logical operations are overloaded between predicates and bitvectors.
class LogicSort (tp :: BaseType) where
  sortAnd :: IsExprBuilder sym => sym -> SymExpr sym tp -> SymExpr sym tp -> IO (SymExpr sym tp)
  sortOr  :: IsExprBuilder sym => sym -> SymExpr sym tp -> SymExpr sym tp -> IO (SymExpr sym tp)
  sortXor :: IsExprBuilder sym => sym -> SymExpr sym tp -> SymExpr sym tp -> IO (SymExpr sym tp)
  sortNot :: IsExprBuilder sym => sym -> SymExpr sym tp -> IO (SymExpr sym tp)

instance LogicSort BaseBoolType where
  sortAnd = WI.andPred
  sortOr  = WI.orPred
  sortXor = WI.xorPred
  sortNot = WI.notPred

instance (1 <= w) => LogicSort (BaseBVType w) where
  sortAnd = WI.bvAndBits
  sortOr  = WI.bvOrBits
  sortXor = WI.bvXorBits
  sortNot = WI.bvNotBits

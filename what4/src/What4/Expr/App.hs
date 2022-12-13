{-|
Module      : What4.Expr.App
Copyright   : (c) Galois Inc, 2015-2020
License     : BSD3
Maintainer  : jhendrix@galois.com

This module defines datastructures that encode the basic
syntax formers used in What4.ExprBuilder.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module What4.Expr.App where

import qualified Control.Exception as Ex
import           Control.Lens hiding (asIndex, (:>), Empty)
import           Control.Monad
import           Control.Monad.ST
import qualified Data.BitVector.Sized as BV
import           Data.Foldable
import           Data.Hashable
import qualified Data.HashTable.Class as H (toList)
import qualified Data.HashTable.ST.Basic as H
import           Data.Kind
import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Classes
import           Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.HashTable as PH
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TH.GADT
import           Data.Parameterized.TraversableFC
import           Data.Ratio (numerator, denominator)
import qualified Data.Sequence as Seq
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.STRef
import           Data.String
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Word (Word64)
import           GHC.Generics (Generic)
import           LibBF (BigFloat)
import qualified LibBF as BF
import           Numeric.Natural
import           Prettyprinter hiding (Unbounded)

import           What4.BaseTypes
import           What4.Concrete
import           What4.Interface
import           What4.ProgramLoc
import qualified What4.SemiRing as SR
import qualified What4.SpecialFunctions as SFn
import qualified What4.Expr.ArrayUpdateMap as AUM
import           What4.Expr.BoolMap (BoolMap, Polarity(..), BoolMapView(..), Wrap(..))
import qualified What4.Expr.BoolMap as BM
import           What4.Expr.MATLAB
import           What4.Expr.WeightedSum (WeightedSum, SemiRingProduct)
import qualified What4.Expr.WeightedSum as WSum
import qualified What4.Expr.StringSeq as SSeq
import           What4.Expr.UnaryBV (UnaryBV)
import qualified What4.Expr.UnaryBV as UnaryBV

import           What4.Utils.AbstractDomains
import           What4.Utils.Arithmetic
import qualified What4.Utils.BVDomain as BVD
import           What4.Utils.Complex
import           What4.Utils.IncrHash
import qualified What4.Utils.AnnotatedMap as AM

------------------------------------------------------------------------
-- Data types

-- | This type represents 'Expr' values that were built from a
-- 'NonceApp'.
--
-- Parameter @t@ is a phantom type brand used to track nonces.
--
-- Selector functions are provided to destruct 'NonceAppExpr' values,
-- but the constructor is kept hidden. The preferred way to construct
-- an 'Expr' from a 'NonceApp' is to use 'sbNonceExpr'.
data NonceAppExpr t (tp :: BaseType)
   = NonceAppExprCtor { nonceExprId  :: {-# UNPACK #-} !(Nonce t tp)
                     , nonceExprLoc :: !ProgramLoc
                     , nonceExprApp :: !(NonceApp t (Expr t) tp)
                     , nonceExprAbsValue :: !(AbstractValue tp)
                     }

-- | This type represents 'Expr' values that were built from an 'App'.
--
-- Parameter @t@ is a phantom type brand used to track nonces.
--
-- Selector functions are provided to destruct 'AppExpr' values, but
-- the constructor is kept hidden. The preferred way to construct an
-- 'Expr' from an 'App' is to use 'sbMakeExpr'.
data AppExpr t (tp :: BaseType)
   = AppExprCtor { appExprId  :: {-# UNPACK #-} !(Nonce t tp)
                , appExprLoc :: !ProgramLoc
                , appExprApp :: !(App (Expr t) tp)
                , appExprAbsValue :: !(AbstractValue tp)
                }

-- | The main ExprBuilder expression datastructure.  The non-trivial @Expr@
-- values constructed by this module are uniquely identified by a
-- nonce value that is used to explicitly represent sub-term sharing.
-- When traversing the structure of an @Expr@ it is usually very important
-- to memoize computations based on the values of these identifiers to avoid
-- exponential blowups due to shared term structure.
--
-- Type parameter @t@ is a phantom type brand used to relate nonces to
-- a specific nonce generator (similar to the @s@ parameter of the
-- @ST@ monad). The type index @tp@ of kind 'BaseType' indicates the
-- type of the values denoted by the given expression.
--
-- Type @'Expr' t@ instantiates the type family @'SymExpr'
-- ('ExprBuilder' t st)@.
data Expr t (tp :: BaseType) where
  SemiRingLiteral :: !(SR.SemiRingRepr sr) -> !(SR.Coefficient sr) -> !ProgramLoc -> Expr t (SR.SemiRingBase sr)
  BoolExpr :: !Bool -> !ProgramLoc -> Expr t BaseBoolType
  FloatExpr :: !(FloatPrecisionRepr fpp) -> !BigFloat -> !ProgramLoc -> Expr t (BaseFloatType fpp)
  StringExpr :: !(StringLiteral si) -> !ProgramLoc -> Expr t (BaseStringType si)
  -- Application
  AppExpr :: {-# UNPACK #-} !(AppExpr t tp) -> Expr t tp
  -- An atomic predicate
  NonceAppExpr :: {-# UNPACK #-} !(NonceAppExpr t tp) -> Expr t tp
  -- A bound variable
  BoundVarExpr :: !(ExprBoundVar t tp) -> Expr t tp

data BVOrNote w = BVOrNote !IncrHash !(BVD.BVDomain w)

newtype BVOrSet e w = BVOrSet (AM.AnnotatedMap (Wrap e (BaseBVType w)) (BVOrNote w) ())


-- | Type @'App' e tp@ encodes the top-level application of an 'Expr'
-- expression. It includes first-order expression forms that do not
-- bind variables (contrast with 'NonceApp').
--
-- Parameter @e@ is used everywhere a recursive sub-expression would
-- go. Uses of the 'App' type will tie the knot through this
-- parameter. Parameter @tp@ indicates the type of the expression.
data App (e :: BaseType -> Type) (tp :: BaseType) where

  ------------------------------------------------------------------------
  -- Generic operations

  BaseIte ::
    !(BaseTypeRepr tp) ->
    !Integer {- Total number of predicates in this ite tree -} ->
    !(e BaseBoolType) ->
    !(e tp) ->
    !(e tp) ->
    App e tp

  BaseEq ::
    !(BaseTypeRepr tp) ->
    !(e tp) ->
    !(e tp) ->
    App e BaseBoolType

  ------------------------------------------------------------------------
  -- Boolean operations

  -- Invariant: The argument to a NotPred must not be another NotPred.
  NotPred :: !(e BaseBoolType) -> App e BaseBoolType

  -- Invariant: The BoolMap must contain at least two elements. No
  -- element may be a NotPred; negated elements must be represented
  -- with Negative element polarity.
  ConjPred :: !(BoolMap e) -> App e BaseBoolType

  ------------------------------------------------------------------------
  -- Semiring operations

  SemiRingSum ::
    {-# UNPACK #-} !(WeightedSum e sr) ->
    App e (SR.SemiRingBase sr)

  -- A product of semiring values
  --
  -- The ExprBuilder should maintain the invariant that none of the values is
  -- a constant, and hence this denotes a non-linear expression.
  -- Multiplications by scalars should use the 'SemiRingSum' constructor.
  SemiRingProd ::
     {-# UNPACK #-} !(SemiRingProduct e sr) ->
     App e (SR.SemiRingBase sr)

  SemiRingLe
     :: !(SR.OrderedSemiRingRepr sr)
     -> !(e (SR.SemiRingBase sr))
     -> !(e (SR.SemiRingBase sr))
     -> App e BaseBoolType

  ------------------------------------------------------------------------
  -- Basic arithmetic operations

  RealIsInteger :: !(e BaseRealType) -> App e BaseBoolType

  IntDiv :: !(e BaseIntegerType)  -> !(e BaseIntegerType) -> App e BaseIntegerType
  IntMod :: !(e BaseIntegerType)  -> !(e BaseIntegerType) -> App e BaseIntegerType
  IntAbs :: !(e BaseIntegerType)  -> App e BaseIntegerType
  IntDivisible :: !(e BaseIntegerType) -> Natural -> App e BaseBoolType

  RealDiv :: !(e BaseRealType) -> !(e BaseRealType) -> App e BaseRealType

  -- Returns @sqrt(x)@, result is not defined if @x@ is negative.
  RealSqrt :: !(e BaseRealType) -> App e BaseRealType

  ------------------------------------------------------------------------
  -- Operations that introduce irrational numbers.

  RealSpecialFunction ::
    !(SFn.SpecialFunction args) ->
    !(SFn.SpecialFnArgs e BaseRealType args) ->
    App e (BaseRealType)

  --------------------------------
  -- Bitvector operations

  -- Return value of bit at given index.
  BVTestBit :: (1 <= w)
            => !Natural -- Index of bit to test
                        -- (least-significant bit has index 0)
            -> !(e (BaseBVType w))
            -> App e BaseBoolType
  BVSlt :: (1 <= w)
        => !(e (BaseBVType w))
        -> !(e (BaseBVType w))
        -> App e BaseBoolType
  BVUlt :: (1 <= w)
        => !(e (BaseBVType w))
        -> !(e (BaseBVType w))
        -> App e BaseBoolType

  BVOrBits :: (1 <= w) => !(NatRepr w) -> !(BVOrSet e w) -> App e (BaseBVType w)

  -- A unary representation of terms where an integer @i@ is mapped to a
  -- predicate that is true if the unsigned encoding of the value is greater
  -- than or equal to @i@.
  --
  -- The map contains a binding (i -> p_i) when the predicate
  --
  -- As an example, we can encode the value @1@ with the assignment:
  --   { 0 => true ; 2 => false }
  BVUnaryTerm :: (1 <= n)
              => !(UnaryBV (e BaseBoolType) n)
              -> App e (BaseBVType n)

  BVConcat :: (1 <= u, 1 <= v, 1 <= (u+v))
           => !(NatRepr (u+v))
           -> !(e (BaseBVType u))
           -> !(e (BaseBVType v))
           -> App e (BaseBVType (u+v))

  BVSelect :: (1 <= n, idx + n <= w)
              -- First bit to select from (least-significant bit has index 0)
           => !(NatRepr idx)
              -- Number of bits to select, counting up toward more significant bits
           -> !(NatRepr n)
              -- Bitvector to select from.
           -> !(e (BaseBVType w))
           -> App e (BaseBVType n)

  BVFill :: (1 <= w)
         => !(NatRepr w)
         -> !(e BaseBoolType)
         -> App e (BaseBVType w)

  BVUdiv :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)
  BVUrem :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)
  BVSdiv :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)
  BVSrem :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)

  BVShl :: (1 <= w)
        => !(NatRepr w)
        -> !(e (BaseBVType w))
        -> !(e (BaseBVType w))
        -> App e (BaseBVType w)

  BVLshr :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)

  BVAshr :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)

  BVRol :: (1 <= w)
        => !(NatRepr w)
        -> !(e (BaseBVType w)) -- bitvector to rotate
        -> !(e (BaseBVType w)) -- rotate amount
        -> App e (BaseBVType w)

  BVRor :: (1 <= w)
        => !(NatRepr w)
        -> !(e (BaseBVType w))   -- bitvector to rotate
        -> !(e (BaseBVType w))   -- rotate amount
        -> App e (BaseBVType w)

  BVZext :: (1 <= w, w+1 <= r, 1 <= r)
         => !(NatRepr r)
         -> !(e (BaseBVType w))
         -> App e (BaseBVType r)

  BVSext :: (1 <= w, w+1 <= r, 1 <= r)
         => !(NatRepr r)
         -> !(e (BaseBVType w))
         -> App e (BaseBVType r)

  BVPopcount ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(e (BaseBVType w)) ->
    App e (BaseBVType w)

  BVCountTrailingZeros ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(e (BaseBVType w)) ->
    App e (BaseBVType w)

  BVCountLeadingZeros ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(e (BaseBVType w)) ->
    App e (BaseBVType w)

  --------------------------------
  -- Float operations

  FloatNeg
    :: !(FloatPrecisionRepr fpp)
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatAbs
    :: !(FloatPrecisionRepr fpp)
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatSqrt
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatAdd
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatSub
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatMul
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatDiv
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatRem
    :: !(FloatPrecisionRepr fpp)
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatFMA
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatFpEq
    :: !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e BaseBoolType
  FloatLe
    :: !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e BaseBoolType
  FloatLt
    :: !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e BaseBoolType
  FloatIsNaN :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatIsInf :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatIsZero :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatIsPos :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatIsNeg :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatIsSubnorm :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatIsNorm :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatCast
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp'))
    -> App e (BaseFloatType fpp)
  FloatRound
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatFromBinary
    :: (2 <= eb, 2 <= sb)
    => !(FloatPrecisionRepr (FloatingPointPrecision eb sb))
    -> !(e (BaseBVType (eb + sb)))
    -> App e (BaseFloatType (FloatingPointPrecision eb sb))
  FloatToBinary
    :: (2 <= eb, 2 <= sb, 1 <= eb + sb)
    => !(FloatPrecisionRepr (FloatingPointPrecision eb sb))
    -> !(e (BaseFloatType (FloatingPointPrecision eb sb)))
    -> App e (BaseBVType (eb + sb))
  BVToFloat
    :: (1 <= w)
    => !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseBVType w))
    -> App e (BaseFloatType fpp)
  SBVToFloat
    :: (1 <= w)
    => !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseBVType w))
    -> App e (BaseFloatType fpp)
  RealToFloat
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e BaseRealType)
    -> App e (BaseFloatType fpp)
  FloatToBV
    :: (1 <= w)
    => !(NatRepr w)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> App e (BaseBVType w)
  FloatToSBV
    :: (1 <= w)
    => !(NatRepr w)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> App e (BaseBVType w)
  FloatToReal :: !(e (BaseFloatType fpp)) -> App e BaseRealType

  FloatSpecialFunction ::
    !(FloatPrecisionRepr fpp) ->
    !(SFn.SpecialFunction args) ->
    !(SFn.SpecialFnArgs e (BaseFloatType fpp) args) ->
    App e (BaseFloatType fpp)

  ------------------------------------------------------------------------
  -- Array operations

  -- Partial map from concrete indices to array values over another array.
  ArrayMap :: !(Ctx.Assignment BaseTypeRepr (i ::> itp))
           -> !(BaseTypeRepr tp)
                -- /\ The type of the array.
           -> !(AUM.ArrayUpdateMap e (i ::> itp) tp)
              -- /\ Maps indices that are updated to the associated value.
           -> !(e (BaseArrayType (i::> itp) tp))
              -- /\ The underlying array that has been updated.
           -> App e (BaseArrayType (i ::> itp) tp)

  -- Constant array
  ConstantArray :: !(Ctx.Assignment BaseTypeRepr (i ::> tp))
                -> !(BaseTypeRepr b)
                -> !(e b)
                -> App e (BaseArrayType (i::>tp) b)

  UpdateArray :: !(BaseTypeRepr b)
              -> !(Ctx.Assignment BaseTypeRepr (i::>tp))
              -> !(e (BaseArrayType (i::>tp) b))
              -> !(Ctx.Assignment e (i::>tp))
              -> !(e b)
              -> App e (BaseArrayType (i::>tp) b)

  SelectArray :: !(BaseTypeRepr b)
              -> !(e (BaseArrayType (i::>tp) b))
              -> !(Ctx.Assignment e (i::>tp))
              -> App e b

  CopyArray ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(BaseTypeRepr a) ->
    !(e (BaseArrayType (SingleCtx (BaseBVType w)) a)) {- @dest_arr@ -} ->
    !(e (BaseBVType w)) {- @dest_idx@ -} ->
    !(e (BaseArrayType (SingleCtx (BaseBVType w)) a)) {- @src_arr@ -} ->
    !(e (BaseBVType w)) {- @src_idx@ -} ->
    !(e (BaseBVType w)) {- @len@ -} ->
    !(e (BaseBVType w)) {- @dest_idx + len@ -} ->
    !(e (BaseBVType w)) {- @src_idx + len@ -} ->
    App e (BaseArrayType (SingleCtx (BaseBVType w)) a)

  SetArray ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(BaseTypeRepr a) ->
    !(e (BaseArrayType (SingleCtx (BaseBVType w)) a)) {- @arr@ -} ->
    !(e (BaseBVType w)) {- @idx@ -} ->
    !(e a) {- @val@ -}->
    !(e (BaseBVType w)) {- @len@ -} ->
    !(e (BaseBVType w)) {- @idx + len@ -} ->
    App e (BaseArrayType (SingleCtx (BaseBVType w)) a)

  EqualArrayRange ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(BaseTypeRepr a) ->
    !(e (BaseArrayType (SingleCtx (BaseBVType w)) a)) {- @lhs_arr@ -} ->
    !(e (BaseBVType w)) {- @lhs_idx@ -} ->
    !(e (BaseArrayType (SingleCtx (BaseBVType w)) a)) {- @rhs_arr@ -} ->
    !(e (BaseBVType w)) {- @rhs_idx@ -} ->
    !(e (BaseBVType w)) {- @len@ -} ->
    !(e (BaseBVType w)) {- @lhs_idx + len@ -} ->
    !(e (BaseBVType w)) {- @rhs_idx + len@ -} ->
    App e BaseBoolType

  ------------------------------------------------------------------------
  -- Conversions.

  IntegerToReal :: !(e BaseIntegerType) -> App e BaseRealType

  -- Convert a real value to an integer
  --
  -- Not defined on non-integral reals.
  RealToInteger :: !(e BaseRealType) -> App e BaseIntegerType

  BVToInteger   :: (1 <= w) => !(e (BaseBVType w)) -> App e BaseIntegerType
  SBVToInteger  :: (1 <= w) => !(e (BaseBVType w)) -> App e BaseIntegerType

  -- Converts integer to a bitvector.  The number is interpreted modulo 2^n.
  IntegerToBV  :: (1 <= w) => !(e BaseIntegerType) -> NatRepr w -> App e (BaseBVType w)

  RoundReal :: !(e BaseRealType) -> App e BaseIntegerType
  RoundEvenReal :: !(e BaseRealType) -> App e BaseIntegerType
  FloorReal :: !(e BaseRealType) -> App e BaseIntegerType
  CeilReal  :: !(e BaseRealType) -> App e BaseIntegerType

  ------------------------------------------------------------------------
  -- Complex operations

  Cplx  :: {-# UNPACK #-} !(Complex (e BaseRealType)) -> App e BaseComplexType
  RealPart :: !(e BaseComplexType) -> App e BaseRealType
  ImagPart :: !(e BaseComplexType) -> App e BaseRealType

  ------------------------------------------------------------------------
  -- Strings

  StringContains :: !(e (BaseStringType si))
                 -> !(e (BaseStringType si))
                 -> App e BaseBoolType

  StringIsPrefixOf :: !(e (BaseStringType si))
                 -> !(e (BaseStringType si))
                 -> App e BaseBoolType

  StringIsSuffixOf :: !(e (BaseStringType si))
                 -> !(e (BaseStringType si))
                 -> App e BaseBoolType

  StringIndexOf :: !(e (BaseStringType si))
                -> !(e (BaseStringType si))
                -> !(e BaseIntegerType)
                -> App e BaseIntegerType

  StringSubstring :: !(StringInfoRepr si)
                  -> !(e (BaseStringType si))
                  -> !(e BaseIntegerType)
                  -> !(e BaseIntegerType)
                  -> App e (BaseStringType si)

  StringAppend :: !(StringInfoRepr si)
               -> !(SSeq.StringSeq e si)
               -> App e (BaseStringType si)

  StringLength :: !(e (BaseStringType si))
               -> App e BaseIntegerType

  ------------------------------------------------------------------------
  -- Structs

  -- A struct with its fields.
  StructCtor :: !(Ctx.Assignment BaseTypeRepr flds)
             -> !(Ctx.Assignment e flds)
             -> App e (BaseStructType flds)

  StructField :: !(e (BaseStructType flds))
              -> !(Ctx.Index flds tp)
              -> !(BaseTypeRepr tp)
              -> App e tp

-- | The Kind of a bound variable.
data VarKind
  = QuantifierVarKind
    -- ^ A variable appearing in a quantifier.
  | LatchVarKind
    -- ^ A variable appearing as a latch input.
  | UninterpVarKind
    -- ^ A variable appearing in a uninterpreted constant

-- | Information about bound variables.
-- Parameter @t@ is a phantom type brand used to track nonces.
--
-- Type @'ExprBoundVar' t@ instantiates the type family
-- @'BoundVar' ('ExprBuilder' t st)@.
--
-- Selector functions are provided to destruct 'ExprBoundVar'
-- values, but the constructor is kept hidden. The preferred way to
-- construct a 'ExprBoundVar' is to use 'freshBoundVar'.
data ExprBoundVar t (tp :: BaseType) =
  BVar { bvarId  :: {-# UNPACK #-} !(Nonce t tp)
       , bvarLoc :: !ProgramLoc
       , bvarName :: !SolverSymbol
       , bvarType :: !(BaseTypeRepr tp)
       , bvarKind :: !VarKind
       , bvarAbstractValue :: !(Maybe (AbstractValue tp))
       }

-- | Type @NonceApp t e tp@ encodes the top-level application of an
-- 'Expr'. It includes expression forms that bind variables (contrast
-- with 'App').
--
-- Parameter @t@ is a phantom type brand used to track nonces.
-- Parameter @e@ is used everywhere a recursive sub-expression would
-- go. Uses of the 'NonceApp' type will tie the knot through this
-- parameter. Parameter @tp@ indicates the type of the expression.
data NonceApp t (e :: BaseType -> Type) (tp :: BaseType) where
  Annotation ::
    !(BaseTypeRepr tp) ->
    !(Nonce t tp) ->
    !(e tp) ->
    NonceApp t e tp

  Forall :: !(ExprBoundVar t tp)
         -> !(e BaseBoolType)
         -> NonceApp t e BaseBoolType
  Exists :: !(ExprBoundVar t tp)
         -> !(e BaseBoolType)
         -> NonceApp t e BaseBoolType

  -- Create an array from a function
  ArrayFromFn :: !(ExprSymFn t (idx ::> itp) ret)
              -> NonceApp t e (BaseArrayType (idx ::> itp) ret)

  -- Create an array by mapping over one or more existing arrays.
  MapOverArrays :: !(ExprSymFn t (ctx::>d) r)
                -> !(Ctx.Assignment BaseTypeRepr (idx ::> itp))
                -> !(Ctx.Assignment (ArrayResultWrapper e (idx ::> itp)) (ctx::>d))
                -> NonceApp t e (BaseArrayType (idx ::> itp) r)

  -- This returns true if all the indices satisfying the given predicate equal true.
  ArrayTrueOnEntries
    :: !(ExprSymFn t (idx ::> itp) BaseBoolType)
    -> !(e (BaseArrayType (idx ::> itp) BaseBoolType))
    -> NonceApp t e BaseBoolType

  -- Apply a function to some arguments
  FnApp :: !(ExprSymFn t args ret)
        -> !(Ctx.Assignment e args)
        -> NonceApp t e ret

-- | This describes information about an undefined or defined function.
-- Parameter @t@ is a phantom type brand used to track nonces.
-- The @args@ and @ret@ parameters define the types of arguments
-- and the return type of the function.
data SymFnInfo t (args :: Ctx BaseType) (ret :: BaseType)
   = UninterpFnInfo !(Ctx.Assignment BaseTypeRepr args)
                    !(BaseTypeRepr ret)
     -- ^ Information about the argument type and return type of an uninterpreted function.

   | DefinedFnInfo !(Ctx.Assignment (ExprBoundVar t) args)
                   !(Expr t ret)
                   !UnfoldPolicy
     -- ^ Information about a defined function.
     -- Includes bound variables and an expression associated to a defined function,
     -- as well as a policy for when to unfold the body.

   | MatlabSolverFnInfo !(MatlabSolverFn (Expr t) args ret)
                        !(Ctx.Assignment (ExprBoundVar t) args)
                        !(Expr t ret)
     -- ^ This is a function that corresponds to a matlab solver function.
     --   It includes the definition as a ExprBuilder expr to
     --   enable export to other solvers.

-- | This represents a symbolic function in the simulator.
-- Parameter @t@ is a phantom type brand used to track nonces.
-- The @args@ and @ret@ parameters define the types of arguments
-- and the return type of the function.
--
-- Type @'ExprSymFn' t (Expr t)@ instantiates the type family @'SymFn'
-- ('ExprBuilder' t st)@.
data ExprSymFn t (args :: Ctx BaseType) (ret :: BaseType)
   = ExprSymFn { symFnId :: !(Nonce t (args ::> ret))
                 -- /\ A unique identifier for the function
                 , symFnName :: !SolverSymbol
                 -- /\ Name of the function
                 , symFnInfo :: !(SymFnInfo t args ret)
                 -- /\ Information about function
                 , symFnLoc  :: !ProgramLoc
                 -- /\ Location where function was defined.
                 }

------------------------------------------------------------------------
-- Template Haskell–generated definitions

-- Dummy declaration splice to bring App into template haskell scope.
$(return [])

-- | Used to implement foldMapFc from traversal.
data Dummy (tp :: k)

instance Eq (Dummy tp) where
  _ == _ = True
instance EqF Dummy where
  eqF _ _ = True
instance TestEquality Dummy where
  testEquality x _y = case x of {}

instance Ord (Dummy tp) where
  compare _ _ = EQ
instance OrdF Dummy where
  compareF x _y = case x of {}

instance HashableF Dummy where
  hashWithSaltF _ _ = 0

instance HasAbsValue Dummy where
  getAbsValue _ = error "you made a magic Dummy value!"

instance FoldableFC App where
  foldMapFC f0 t = getConst (traverseApp (g f0) t)
    where g :: (f tp -> a) -> f tp -> Const a (Dummy tp)
          g f v = Const (f v)

traverseApp :: (Applicative m, OrdF f, Eq (f (BaseBoolType)), HashableF f, HasAbsValue f)
            => (forall tp. e tp -> m (f tp))
            -> App e utp -> m ((App f) utp)
traverseApp =
  $(structuralTraversal [t|App|]
    [ ( ConType [t|UnaryBV|] `TypeApp` AnyType `TypeApp` AnyType
      , [|UnaryBV.instantiate|]
      )
    , ( ConType [t|Ctx.Assignment BaseTypeRepr|] `TypeApp` AnyType
      , [|(\_ -> pure) |]
      )
    , ( ConType [t|WeightedSum|] `TypeApp` AnyType `TypeApp` AnyType
      , [| WSum.traverseVars |]
      )
    , ( ConType [t|BVOrSet|] `TypeApp` AnyType `TypeApp` AnyType
      , [| traverseBVOrSet |]
      )
    , ( ConType [t|SemiRingProduct|] `TypeApp` AnyType `TypeApp` AnyType
      , [| WSum.traverseProdVars |]
      )
    , ( ConType [t|AUM.ArrayUpdateMap|] `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType
      , [| AUM.traverseArrayUpdateMap |]
      )
    , ( ConType [t|SSeq.StringSeq|] `TypeApp` AnyType `TypeApp` AnyType
      , [| SSeq.traverseStringSeq |]
      )
    , ( ConType [t|BoolMap|] `TypeApp` AnyType
      , [| BM.traverseVars |]
      )
    , ( ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType
      , [| traverseFC |]
      )
    , ( ConType [t|SFn.SpecialFnArgs|] `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType
      , [| SFn.traverseSpecialFnArgs |]
      )
    ]
   )

{-# NOINLINE appEqF #-}
-- | Check if two applications are equal.
appEqF ::
  (Eq (e BaseBoolType), Eq (e BaseRealType), HashableF e, HasAbsValue e, OrdF e) =>
  App e x -> App e y -> Maybe (x :~: y)
appEqF = $(structuralTypeEquality [t|App|]
           [ (TypeApp (ConType [t|NatRepr|]) AnyType, [|testEquality|])
           , (TypeApp (ConType [t|FloatPrecisionRepr|]) AnyType, [|testEquality|])
           , (TypeApp (ConType [t|BaseTypeRepr|]) AnyType, [|testEquality|])
           , (DataArg 0 `TypeApp` AnyType, [|testEquality|])
           , (ConType [t|UnaryBV|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|AUM.ArrayUpdateMap|] `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType
             , [|\x y -> if x == y then Just Refl else Nothing|])
           , (ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|Ctx.Index|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|StringInfoRepr|] `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|SR.SemiRingRepr|] `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|SR.OrderedSemiRingRepr|] `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|SFn.SpecialFunction|] `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|WSum.WeightedSum|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|SemiRingProduct|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|])
           ]
          )

instance (Eq (e BaseBoolType), Eq (e BaseRealType), HashableF e, HasAbsValue e, OrdF e) => Eq (App e tp) where
  x == y = isJust (testEquality x y)

instance (Eq (e BaseBoolType), Eq (e BaseRealType), HashableF e, HasAbsValue e, OrdF e) => TestEquality (App e) where
  testEquality = appEqF

{-# NOINLINE hashApp #-}
-- | Hash an an application.
hashApp ::
  (OrdF e, HashableF e, HasAbsValue e, Hashable (e BaseBoolType), Hashable (e BaseRealType)) =>
  Int -> App e s -> Int
hashApp = $(structuralHashWithSalt [t|App|]
               [(DataArg 0 `TypeApp` AnyType, [|hashWithSaltF|])]
           )

instance (OrdF e, HashableF e, HasAbsValue e, Hashable (e BaseBoolType), Hashable (e BaseRealType)) =>
  HashableF (App e) where
    hashWithSaltF = hashApp


-- | Return 'true' if an app represents a non-linear operation.
-- Controls whether the non-linear counter ticks upward in the
-- 'Statistics'.
isNonLinearApp :: App e tp -> Bool
isNonLinearApp app = case app of
  -- FIXME: These are just guesses; someone who knows what's actually
  -- slow in the solvers should correct them.

  SemiRingProd pd
    | SR.SemiRingBVRepr SR.BVBitsRepr _ <- WSum.prodRepr pd -> False
    | otherwise -> True

  IntDiv {} -> True
  IntMod {} -> True
  IntDivisible {} -> True

  RealDiv {} -> True
  RealSqrt {} -> True
  RealSpecialFunction{} -> True

  BVUdiv {} -> True
  BVUrem {} -> True
  BVSdiv {} -> True
  BVSrem {} -> True

  FloatSqrt {} -> True
  FloatMul {} -> True
  FloatDiv {} -> True
  FloatRem {} -> True
  FloatSpecialFunction{} -> True

  _ -> False



instance TestEquality e => Eq (NonceApp t e tp) where
  x == y = isJust (testEquality x y)

instance TestEquality e => TestEquality (NonceApp t e) where
  testEquality =
    $(structuralTypeEquality [t|NonceApp|]
           [ (DataArg 0 `TypeApp` AnyType, [|testEquality|])
           , (DataArg 1 `TypeApp` AnyType, [|testEquality|])
           , ( ConType [t|BaseTypeRepr|] `TypeApp` AnyType
             , [|testEquality|]
             )
           , ( ConType [t|Nonce|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|]
             )
           , ( ConType [t|ExprBoundVar|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|]
             )
           , ( ConType [t|ExprSymFn|] `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType
              , [|testExprSymFnEq|]
              )
           , ( ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|]
             )
           ]
          )

instance (HashableF e, TestEquality e) => HashableF (NonceApp t e) where
  hashWithSaltF = $(structuralHashWithSalt [t|NonceApp|]
                      [ (DataArg 1 `TypeApp` AnyType, [|hashWithSaltF|]) ])

traverseArrayResultWrapper
  :: Functor m
  => (forall tp . e tp -> m (f tp))
     -> ArrayResultWrapper e (idx ::> itp) c
     -> m (ArrayResultWrapper f (idx ::> itp) c)
traverseArrayResultWrapper f (ArrayResultWrapper a) =
  ArrayResultWrapper <$> f a

traverseArrayResultWrapperAssignment
  :: Applicative m
  => (forall tp . e tp -> m (f tp))
     -> Ctx.Assignment (ArrayResultWrapper e (idx ::> itp)) c
     -> m (Ctx.Assignment (ArrayResultWrapper f (idx ::> itp)) c)
traverseArrayResultWrapperAssignment f = traverseFC (\e -> traverseArrayResultWrapper f e)

instance FunctorFC (NonceApp t)  where
  fmapFC = fmapFCDefault

instance FoldableFC (NonceApp t) where
  foldMapFC = foldMapFCDefault

instance TraversableFC (NonceApp t) where
  traverseFC =
    $(structuralTraversal [t|NonceApp|]
      [ ( ConType [t|Ctx.Assignment|]
          `TypeApp` (ConType [t|ArrayResultWrapper|] `TypeApp` AnyType `TypeApp` AnyType)
          `TypeApp` AnyType
        , [|traverseArrayResultWrapperAssignment|]
        )
      , ( ConType [t|ExprSymFn|] `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType
        , [|\_-> pure|]
        )
      , ( ConType [t|Ctx.Assignment|] `TypeApp` ConType [t|BaseTypeRepr|] `TypeApp` AnyType
        , [|\_ -> pure|]
        )
      , ( ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType
        , [|traverseFC|]
        )
      ]
     )

instance PolyEq (Expr t x) (Expr t y) where
  polyEqF x y = do
    Refl <- testEquality x y
    return Refl

------------------------------------------------------------------------
-- Expr

-- | Destructor for the 'AppExpr' constructor.
{-# INLINE asApp #-}
asApp :: Expr t tp -> Maybe (App (Expr t) tp)
asApp (AppExpr a) = Just (appExprApp a)
asApp _ = Nothing

-- | Destructor for the 'NonceAppExpr' constructor.
{-# INLINE asNonceApp #-}
asNonceApp :: Expr t tp -> Maybe (NonceApp t (Expr t) tp)
asNonceApp (NonceAppExpr a) = Just (nonceExprApp a)
asNonceApp _ = Nothing

exprLoc :: Expr t tp -> ProgramLoc
exprLoc (SemiRingLiteral _ _ l) = l
exprLoc (BoolExpr _ l) = l
exprLoc (FloatExpr _ _ l) = l
exprLoc (StringExpr _ l) = l
exprLoc (NonceAppExpr a)  = nonceExprLoc a
exprLoc (AppExpr a)   = appExprLoc a
exprLoc (BoundVarExpr v) = bvarLoc v

mkExpr :: Nonce t tp
      -> ProgramLoc
      -> App (Expr t) tp
      -> AbstractValue tp
      -> Expr t tp
mkExpr n l a v = AppExpr $ AppExprCtor { appExprId  = n
                                    , appExprLoc = l
                                    , appExprApp = a
                                    , appExprAbsValue = v
                                    }



type BoolExpr t = Expr t BaseBoolType
type FloatExpr t fpp = Expr t (BaseFloatType fpp)
type BVExpr t n = Expr t (BaseBVType n)
type IntegerExpr t = Expr t BaseIntegerType
type RealExpr t = Expr t BaseRealType
type CplxExpr t = Expr t BaseComplexType
type StringExpr t si = Expr t (BaseStringType si)



iteSize :: Expr t tp -> Integer
iteSize e =
  case asApp e of
    Just (BaseIte _ sz _ _ _) -> sz
    _ -> 0

instance IsExpr (Expr t) where
  asConstantPred = exprAbsValue

  asInteger (SemiRingLiteral SR.SemiRingIntegerRepr n _) = Just n
  asInteger _ = Nothing

  integerBounds x = exprAbsValue x

  asRational (SemiRingLiteral SR.SemiRingRealRepr r _) = Just r
  asRational _ = Nothing

  rationalBounds x = ravRange $ exprAbsValue x

  asFloat (FloatExpr _fpp bf _) = Just bf
  asFloat _ = Nothing

  asComplex e
    | Just (Cplx c) <- asApp e = traverse asRational c
    | otherwise = Nothing

  exprType (SemiRingLiteral sr _ _) = SR.semiRingBase sr
  exprType (BoolExpr _ _) = BaseBoolRepr
  exprType (FloatExpr fpp _ _) = BaseFloatRepr fpp
  exprType (StringExpr s _) = BaseStringRepr (stringLiteralInfo s)
  exprType (NonceAppExpr e)  = nonceAppType (nonceExprApp e)
  exprType (AppExpr e) = appType (appExprApp e)
  exprType (BoundVarExpr i) = bvarType i

  asBV (SemiRingLiteral (SR.SemiRingBVRepr _ _) i _) = Just i
  asBV _ = Nothing

  unsignedBVBounds x = Just $ BVD.ubounds $ exprAbsValue x
  signedBVBounds x = Just $ BVD.sbounds (bvWidth x) $ exprAbsValue x

  asAffineVar e = case exprType e of
    BaseIntegerRepr
      | Just (a, x, b) <- WSum.asAffineVar $
          asWeightedSum SR.SemiRingIntegerRepr e ->
        Just (ConcreteInteger a, x, ConcreteInteger b)
    BaseRealRepr
      | Just (a, x, b) <- WSum.asAffineVar $
          asWeightedSum SR.SemiRingRealRepr e ->
        Just (ConcreteReal a, x, ConcreteReal b)
    BaseBVRepr w
      | Just (a, x, b) <- WSum.asAffineVar $
          asWeightedSum (SR.SemiRingBVRepr SR.BVArithRepr (bvWidth e)) e ->
        Just (ConcreteBV w a, x, ConcreteBV w b)
    _ -> Nothing

  asString (StringExpr x _) = Just x
  asString _ = Nothing

  asConstantArray (asApp -> Just (ConstantArray _ _ def)) = Just def
  asConstantArray _ = Nothing

  asStruct (asApp -> Just (StructCtor _ flds)) = Just flds
  asStruct _ = Nothing

  printSymExpr = pretty

  unsafeSetAbstractValue av e =
    case e of
      SemiRingLiteral{} -> e
      BoolExpr{}        -> e
      FloatExpr{}       -> e
      StringExpr{}      -> e
      AppExpr ae        -> AppExpr (ae{appExprAbsValue = av})
      NonceAppExpr nae  -> NonceAppExpr (nae{nonceExprAbsValue = av})
      BoundVarExpr ebv  -> BoundVarExpr (ebv{bvarAbstractValue = Just av})


asSemiRingLit :: SR.SemiRingRepr sr -> Expr t (SR.SemiRingBase sr) -> Maybe (SR.Coefficient sr)
asSemiRingLit sr (SemiRingLiteral sr' x _loc)
  | Just Refl <- testEquality sr sr'
  = Just x

  -- special case, ignore the BV ring flavor for this purpose
  | SR.SemiRingBVRepr _ w  <- sr
  , SR.SemiRingBVRepr _ w' <- sr'
  , Just Refl <- testEquality w w'
  = Just x

asSemiRingLit _ _ = Nothing

asSemiRingSum :: SR.SemiRingRepr sr -> Expr t (SR.SemiRingBase sr) -> Maybe (WeightedSum (Expr t) sr)
asSemiRingSum sr (asSemiRingLit sr -> Just x) = Just (WSum.constant sr x)
asSemiRingSum sr (asApp -> Just (SemiRingSum x))
   | Just Refl <- testEquality sr (WSum.sumRepr x) = Just x
asSemiRingSum _ _ = Nothing

asSemiRingProd :: SR.SemiRingRepr sr -> Expr t (SR.SemiRingBase sr) -> Maybe (SemiRingProduct (Expr t) sr)
asSemiRingProd sr (asApp -> Just (SemiRingProd x))
  | Just Refl <- testEquality sr (WSum.prodRepr x) = Just x
asSemiRingProd _ _ = Nothing

-- | This privides a view of a semiring expr as a weighted sum of values.
data SemiRingView t sr
   = SR_Constant !(SR.Coefficient sr)
   | SR_Sum  !(WeightedSum (Expr t) sr)
   | SR_Prod !(SemiRingProduct (Expr t) sr)
   | SR_General

viewSemiRing:: SR.SemiRingRepr sr -> Expr t (SR.SemiRingBase sr) -> SemiRingView t sr
viewSemiRing sr x
  | Just r <- asSemiRingLit sr x  = SR_Constant r
  | Just s <- asSemiRingSum sr x  = SR_Sum s
  | Just p <- asSemiRingProd sr x = SR_Prod p
  | otherwise = SR_General

asWeightedSum :: HashableF (Expr t) => SR.SemiRingRepr sr -> Expr t (SR.SemiRingBase sr) -> WeightedSum (Expr t) sr
asWeightedSum sr x
  | Just r <- asSemiRingLit sr x = WSum.constant sr r
  | Just s <- asSemiRingSum sr x = s
  | otherwise = WSum.var sr x

asConjunction :: Expr t BaseBoolType -> [(Expr t BaseBoolType, Polarity)]
asConjunction (BoolExpr True _) = []
asConjunction (asApp -> Just (ConjPred xs)) =
 case BM.viewBoolMap xs of
   BoolMapUnit     -> []
   BoolMapDualUnit -> [(BoolExpr False initializationLoc, Positive)]
   BoolMapTerms (tm:|tms) -> tm:tms
asConjunction x = [(x,Positive)]


asDisjunction :: Expr t BaseBoolType -> [(Expr t BaseBoolType, Polarity)]
asDisjunction (BoolExpr False _) = []
asDisjunction (asApp -> Just (NotPred (asApp -> Just (ConjPred xs)))) =
 case BM.viewBoolMap xs of
   BoolMapUnit     -> []
   BoolMapDualUnit -> [(BoolExpr True initializationLoc, Positive)]
   BoolMapTerms (tm:|tms) -> map (over _2 BM.negatePolarity) (tm:tms)
asDisjunction x = [(x,Positive)]

asPosAtom :: Expr t BaseBoolType -> (Expr t BaseBoolType, Polarity)
asPosAtom (asApp -> Just (NotPred x)) = (x, Negative)
asPosAtom x                           = (x, Positive)

asNegAtom :: Expr t BaseBoolType -> (Expr t BaseBoolType, Polarity)
asNegAtom (asApp -> Just (NotPred x)) = (x, Positive)
asNegAtom x                           = (x, Negative)


-- | Get abstract value associated with element.
exprAbsValue :: Expr t tp -> AbstractValue tp
exprAbsValue (SemiRingLiteral sr x _) =
  case sr of
    SR.SemiRingIntegerRepr  -> singleRange x
    SR.SemiRingRealRepr -> ravSingle x
    SR.SemiRingBVRepr _ w -> BVD.singleton w (BV.asUnsigned x)

exprAbsValue (StringExpr l _) = stringAbsSingle l
exprAbsValue (FloatExpr _ _ _) = ()
exprAbsValue (BoolExpr b _)   = Just b
exprAbsValue (NonceAppExpr e) = nonceExprAbsValue e
exprAbsValue (AppExpr e)      = appExprAbsValue e
exprAbsValue (BoundVarExpr v) =
  fromMaybe (unconstrainedAbsValue (bvarType v)) (bvarAbstractValue v)

instance HasAbsValue (Expr t) where
  getAbsValue = exprAbsValue


------------------------------------------------------------------------
-- Expr operations

{-# INLINE compareExpr #-}
compareExpr :: Expr t x -> Expr t y -> OrderingF x y

-- Special case, ignore the BV semiring flavor for this purpose
compareExpr (SemiRingLiteral (SR.SemiRingBVRepr _ wx) x _) (SemiRingLiteral (SR.SemiRingBVRepr _ wy) y _) =
  case compareF wx wy of
    LTF -> LTF
    EQF -> fromOrdering (compare x y)
    GTF -> GTF
compareExpr (SemiRingLiteral srx x _) (SemiRingLiteral sry y _) =
  case compareF srx sry of
    LTF -> LTF
    EQF -> fromOrdering (SR.sr_compare srx x y)
    GTF -> GTF
compareExpr SemiRingLiteral{} _ = LTF
compareExpr _ SemiRingLiteral{} = GTF

compareExpr (StringExpr x _) (StringExpr y _) =
  case compareF x y of
    LTF -> LTF
    EQF -> EQF
    GTF -> GTF

compareExpr StringExpr{} _ = LTF
compareExpr _ StringExpr{} = GTF

compareExpr (BoolExpr x _) (BoolExpr y _) = fromOrdering (compare x y)
compareExpr BoolExpr{} _ = LTF
compareExpr _ BoolExpr{} = GTF

compareExpr (FloatExpr rx x _) (FloatExpr ry y _) =
   case compareF rx ry of
     LTF -> LTF
     EQF -> fromOrdering (BF.bfCompare x y) -- NB, don't use `compare`, which is IEEE754 comaprison
     GTF -> GTF

compareExpr FloatExpr{} _ = LTF
compareExpr _ FloatExpr{} = GTF

compareExpr (NonceAppExpr x) (NonceAppExpr y) = compareF x y
compareExpr NonceAppExpr{} _ = LTF
compareExpr _ NonceAppExpr{} = GTF

compareExpr (AppExpr x) (AppExpr y) = compareF (appExprId x) (appExprId y)
compareExpr AppExpr{} _ = LTF
compareExpr _ AppExpr{} = GTF

compareExpr (BoundVarExpr x) (BoundVarExpr y) = compareF x y

-- | A slightly more aggressive syntactic equality check than testEquality,
--   `sameTerm` will recurse through a small collection of known syntax formers.
sameTerm :: Expr t a -> Expr t b -> Maybe (a :~: b)

sameTerm (asApp -> Just (FloatToBinary fppx x)) (asApp -> Just (FloatToBinary fppy y)) =
  do Refl <- testEquality fppx fppy
     Refl <- sameTerm x y
     return Refl

sameTerm x y = testEquality x y


instance TestEquality (NonceAppExpr t) where
  testEquality x y =
    case compareF x y of
      EQF -> Just Refl
      _ -> Nothing

instance OrdF (NonceAppExpr t)  where
  compareF x y = compareF (nonceExprId x) (nonceExprId y)

instance Eq (NonceAppExpr t tp) where
  x == y = isJust (testEquality x y)

instance Ord (NonceAppExpr t tp) where
  compare x y = toOrdering (compareF x y)

instance TestEquality (Expr t) where
  testEquality x y =
    case compareF x y of
      EQF -> Just Refl
      _ -> Nothing

instance OrdF (Expr t)  where
  compareF = compareExpr

instance Eq (Expr t tp) where
  x == y = isJust (testEquality x y)

instance Ord (Expr t tp) where
  compare x y = toOrdering (compareF x y)

instance Hashable (Expr t tp) where
  hashWithSalt s (BoolExpr b _) = hashWithSalt (hashWithSalt s (0::Int)) b
  hashWithSalt s (SemiRingLiteral sr x _) =
    case sr of
      SR.SemiRingIntegerRepr -> hashWithSalt (hashWithSalt s (2::Int)) x
      SR.SemiRingRealRepr    -> hashWithSalt (hashWithSalt s (3::Int)) x
      SR.SemiRingBVRepr _ w  -> hashWithSalt (hashWithSaltF (hashWithSalt s (4::Int)) w) x

  hashWithSalt s (FloatExpr fr x _) = hashWithSalt (hashWithSaltF (hashWithSalt s (5::Int)) fr) x
  hashWithSalt s (StringExpr x _) = hashWithSalt (hashWithSalt s (6::Int)) x
  hashWithSalt s (AppExpr x)      = hashWithSalt (hashWithSalt s (7::Int)) (appExprId x)
  hashWithSalt s (NonceAppExpr x) = hashWithSalt (hashWithSalt s (8::Int)) (nonceExprId x)
  hashWithSalt s (BoundVarExpr x) = hashWithSalt (hashWithSalt s (9::Int)) x

instance PH.HashableF (Expr t) where
  hashWithSaltF = hashWithSalt


------------------------------------------------------------------------
-- PPIndex

data PPIndex
   = ExprPPIndex {-# UNPACK #-} !Word64
   | RatPPIndex !Rational
  deriving (Eq, Ord, Generic)

instance Hashable PPIndex

------------------------------------------------------------------------
-- countOccurrences

countOccurrences :: Expr t tp -> Map.Map PPIndex Int
countOccurrences e0 = runST $ do
  visited <- H.new
  countOccurrences' visited e0
  Map.fromList <$> H.toList visited

type OccurrenceTable s = H.HashTable s PPIndex Int


incOccurrence :: OccurrenceTable s -> PPIndex -> ST s () -> ST s ()
incOccurrence visited idx sub = do
  mv <- H.lookup visited idx
  case mv of
    Just i -> H.insert visited idx $! i+1
    Nothing -> sub >> H.insert visited idx 1

-- FIXME... why does this ignore Nat and Int literals?
countOccurrences' :: forall t tp s . OccurrenceTable s -> Expr t tp -> ST s ()
countOccurrences' visited (SemiRingLiteral SR.SemiRingRealRepr r _) = do
  incOccurrence visited (RatPPIndex r) $
    return ()
countOccurrences' visited (AppExpr e) = do
  let idx = ExprPPIndex (indexValue (appExprId e))
  incOccurrence visited idx $ do
    traverseFC_ (countOccurrences' visited) (appExprApp e)
countOccurrences' visited (NonceAppExpr e) = do
  let idx = ExprPPIndex (indexValue (nonceExprId e))
  incOccurrence visited idx $ do
    traverseFC_ (countOccurrences' visited) (nonceExprApp e)
countOccurrences' _ _ = return ()

------------------------------------------------------------------------
-- boundVars

type BoundVarMap s t = H.HashTable s PPIndex (Set (Some (ExprBoundVar t)))

cache :: (Eq k, Hashable k) => H.HashTable s k r -> k -> ST s r -> ST s r
cache h k m = do
  mr <- H.lookup h k
  case mr of
    Just r -> return r
    Nothing -> do
      r <- m
      H.insert h k r
      return r


boundVars :: Expr t tp -> ST s (BoundVarMap s t)
boundVars e0 = do
  visited <- H.new
  _ <- boundVars' visited e0
  return visited

boundVars' :: BoundVarMap s t
           -> Expr t tp
           -> ST s (Set (Some (ExprBoundVar t)))
boundVars' visited (AppExpr e) = do
  let idx = indexValue (appExprId e)
  cache visited (ExprPPIndex idx) $ do
    sums <- sequence (toListFC (boundVars' visited) (appExprApp e))
    return $ foldl' Set.union Set.empty sums
boundVars' visited (NonceAppExpr e) = do
  let idx = indexValue (nonceExprId e)
  cache visited (ExprPPIndex idx) $ do
    sums <- sequence (toListFC (boundVars' visited) (nonceExprApp e))
    return $ foldl' Set.union Set.empty sums
boundVars' visited (BoundVarExpr v)
  | QuantifierVarKind <- bvarKind v = do
      let idx = indexValue (bvarId v)
      cache visited (ExprPPIndex idx) $
        return (Set.singleton (Some v))
boundVars' _ _ = return Set.empty


------------------------------------------------------------------------
-- Pretty printing

instance Show (Expr t tp) where
  show = show . ppExpr

instance Pretty (Expr t tp) where
  pretty = ppExpr



-- | @AppPPExpr@ represents a an application, and it may be let bound.
data AppPPExpr ann
   = APE { apeIndex :: !PPIndex
         , apeLoc :: !ProgramLoc
         , apeName :: !Text
         , apeExprs :: ![PPExpr ann]
         , apeLength :: !Int
           -- ^ Length of AppPPExpr not including parenthesis.
         }

data PPExpr ann
   = FixedPPExpr !(Doc ann) ![Doc ann] !Int
     -- ^ A fixed doc with length.
   | AppPPExpr !(AppPPExpr ann)
     -- ^ A doc that can be let bound.

-- | Pretty print a AppPPExpr
apeDoc :: AppPPExpr ann -> (Doc ann, [Doc ann])
apeDoc a = (pretty (apeName a), ppExprDoc True <$> apeExprs a)

textPPExpr :: Text -> PPExpr ann
textPPExpr t = FixedPPExpr (pretty t) [] (Text.length t)

stringPPExpr :: String -> PPExpr ann
stringPPExpr t = FixedPPExpr (pretty t) [] (length t)

-- | Get length of Expr including parens.
ppExprLength :: PPExpr ann -> Int
ppExprLength (FixedPPExpr _ [] n) = n
ppExprLength (FixedPPExpr _ _ n) = n + 2
ppExprLength (AppPPExpr a) = apeLength a + 2

parenIf :: Bool -> Doc ann -> [Doc ann] -> Doc ann
parenIf _ h [] = h
parenIf False h l = hsep (h:l)
parenIf True h l = parens (hsep (h:l))

-- | Pretty print PPExpr
ppExprDoc :: Bool -> PPExpr ann -> Doc ann
ppExprDoc b (FixedPPExpr d a _) = parenIf b d a
ppExprDoc b (AppPPExpr a) = uncurry (parenIf b) (apeDoc a)

data PPExprOpts = PPExprOpts { ppExpr_maxWidth :: Int
                           , ppExpr_useDecimal :: Bool
                           }

defaultPPExprOpts :: PPExprOpts
defaultPPExprOpts =
  PPExprOpts { ppExpr_maxWidth = 68
            , ppExpr_useDecimal = True
            }

-- | Pretty print an 'Expr' using let bindings to create the term.
ppExpr :: Expr t tp -> Doc ann
ppExpr e
     | Prelude.null bindings = ppExprDoc False r
     | otherwise =
       vsep
       [ "let" <+> align (vcat bindings)
       , " in" <+> align (ppExprDoc False r) ]
  where (bindings,r) = runST (ppExpr' e defaultPPExprOpts)

instance ShowF (Expr t)

-- | Pretty print the top part of an element.
ppExprTop :: Expr t tp -> Doc ann
ppExprTop e = ppExprDoc False r
  where (_,r) = runST (ppExpr' e defaultPPExprOpts)

-- | Contains the elements before, the index, doc, and width and
-- the elements after.
type SplitPPExprList ann = Maybe ([PPExpr ann], AppPPExpr ann, [PPExpr ann])

findExprToRemove :: [PPExpr ann] -> SplitPPExprList ann
findExprToRemove exprs0 = go [] exprs0 Nothing
  where go :: [PPExpr ann] -> [PPExpr ann] -> SplitPPExprList ann -> SplitPPExprList ann
        go _ [] mr = mr
        go prev (e@FixedPPExpr{} : exprs) mr = do
          go (e:prev) exprs mr
        go prev (AppPPExpr a:exprs) mr@(Just (_,a',_))
          | apeLength a < apeLength a' = go (AppPPExpr a:prev) exprs mr
        go prev (AppPPExpr a:exprs) _ = do
          go (AppPPExpr a:prev) exprs (Just (reverse prev, a, exprs))


ppExpr' :: forall t tp s ann. Expr t tp -> PPExprOpts -> ST s ([Doc ann], PPExpr ann)
ppExpr' e0 o = do
  let max_width = ppExpr_maxWidth o
  let use_decimal = ppExpr_useDecimal o
  -- Get map that counts number of elements.
  let m = countOccurrences e0
  -- Return number of times a term is referred to in dag.
  let isShared :: PPIndex -> Bool
      isShared w = fromMaybe 0 (Map.lookup w m) > 1

  -- Get bounds variables.
  bvars <- boundVars e0

  bindingsRef <- newSTRef Seq.empty

  visited <- H.new :: ST s (H.HashTable s PPIndex (PPExpr ann))
  visited_fns <- H.new :: ST s (H.HashTable s Word64 Text)

  let -- Add a binding to the list of bindings
      addBinding :: AppPPExpr ann -> ST s (PPExpr ann)
      addBinding a = do
        let idx = apeIndex a
        cnt <- Seq.length <$> readSTRef bindingsRef

        vars <- fromMaybe Set.empty <$> H.lookup bvars idx
        -- TODO: avoid intermediate String from 'ppBoundVar'
        let args :: [String]
            args = viewSome ppBoundVar <$> Set.toList vars

        let nm = case idx of
                   ExprPPIndex e -> "v" ++ show e
                   RatPPIndex _ -> "r" ++ show cnt
        let lhs = parenIf False (pretty nm) (pretty <$> args)
        let doc = vcat
                  [ "--" <+> pretty (plSourceLoc (apeLoc a))
                  , lhs <+> "=" <+> uncurry (parenIf False) (apeDoc a) ]
        modifySTRef' bindingsRef (Seq.|> doc)
        let len = length nm + sum ((\arg_s -> length arg_s + 1) <$> args)
        let nm_expr = FixedPPExpr (pretty nm) (map pretty args) len
        H.insert visited idx $! nm_expr
        return nm_expr

  let fixLength :: Int
                -> [PPExpr ann]
                -> ST s ([PPExpr ann], Int)
      fixLength cur_width exprs
        | cur_width > max_width
        , Just (prev_e, a, next_e) <- findExprToRemove exprs = do
          r <- addBinding a
          let exprs' = prev_e ++ [r] ++ next_e
          fixLength (cur_width - apeLength a + ppExprLength r) exprs'
      fixLength cur_width exprs = do
        return $! (exprs, cur_width)

  -- Pretty print an argument.
  let renderArg :: PrettyArg (Expr t) -> ST s (PPExpr ann)
      renderArg (PrettyArg e) = getBindings e
      renderArg (PrettyText txt) = return (textPPExpr txt)
      renderArg (PrettyFunc nm args) =
        do exprs0 <- traverse renderArg args
           let total_width = Text.length nm + sum ((\e -> 1 + ppExprLength e) <$> exprs0)
           (exprs1, cur_width) <- fixLength total_width exprs0
           let exprs = map (ppExprDoc True) exprs1
           return (FixedPPExpr (pretty nm) exprs cur_width)

      renderApp :: PPIndex
                -> ProgramLoc
                -> Text
                -> [PrettyArg (Expr t)]
                -> ST s (AppPPExpr ann)
      renderApp idx loc nm args = Ex.assert (not (Prelude.null args)) $ do
        exprs0 <- traverse renderArg args
        -- Get width not including parenthesis of outer app.
        let total_width = Text.length nm + sum ((\e -> 1 + ppExprLength e) <$> exprs0)
        (exprs, cur_width) <- fixLength total_width exprs0
        return APE { apeIndex = idx
                   , apeLoc = loc
                   , apeName = nm
                   , apeExprs = exprs
                   , apeLength = cur_width
                   }

      cacheResult :: PPIndex
                  -> ProgramLoc
                  -> PrettyApp (Expr t)
                  -> ST s (PPExpr ann)
      cacheResult _ _ (nm,[]) = do
        return (textPPExpr nm)
      cacheResult idx loc (nm,args) = do
        mr <- H.lookup visited idx
        case mr of
          Just d -> return d
          Nothing -> do
            a <- renderApp idx loc nm args
            if isShared idx then
              addBinding a
             else
              return (AppPPExpr a)

      bindFn :: ExprSymFn t idx ret -> ST s (PrettyArg (Expr t))
      bindFn f = do
        let idx = indexValue (symFnId f)
        mr <- H.lookup visited_fns idx
        case mr of
          Just d -> return (PrettyText d)
          Nothing -> do
            case symFnInfo f of
              UninterpFnInfo{} -> do
                let def_doc = viaShow f <+> "=" <+> "??"
                modifySTRef' bindingsRef (Seq.|> def_doc)
              DefinedFnInfo vars rhs _ -> do
                -- TODO: avoid intermediate String from 'ppBoundVar'
                let pp_vars = toListFC (pretty . ppBoundVar) vars
                let def_doc = viaShow f <+> hsep pp_vars <+> "=" <+> ppExpr rhs
                modifySTRef' bindingsRef (Seq.|> def_doc)
              MatlabSolverFnInfo fn_id _ _ -> do
                let def_doc = viaShow f <+> "=" <+> ppMatlabSolverFn fn_id
                modifySTRef' bindingsRef (Seq.|> def_doc)

            let d = Text.pack (show f)
            H.insert visited_fns idx $! d
            return $! PrettyText d

      -- Collect definitions for all applications that occur multiple times
      -- in term.
      getBindings :: Expr t u -> ST s (PPExpr ann)
      getBindings (SemiRingLiteral sr x l) =
        case sr of
          SR.SemiRingIntegerRepr ->
            return $ stringPPExpr (show x)
          SR.SemiRingRealRepr -> cacheResult (RatPPIndex x) l app
             where n = numerator x
                   d = denominator x
                   app | d == 1      = prettyApp (fromString (show n)) []
                       | use_decimal = prettyApp (fromString (show (fromRational x :: Double))) []
                       | otherwise   = prettyApp "divReal"  [ showPrettyArg n, showPrettyArg d ]
          SR.SemiRingBVRepr _ w ->
            return $ stringPPExpr $ BV.ppHex w x

      getBindings (StringExpr x _) =
        return $ stringPPExpr $ (show x)
      getBindings (FloatExpr _ f _) =
        return $ stringPPExpr (show f)
      getBindings (BoolExpr b _) =
        return $ stringPPExpr (if b then "true" else "false")
      getBindings (NonceAppExpr e) =
        cacheResult (ExprPPIndex (indexValue (nonceExprId e))) (nonceExprLoc e)
          =<< ppNonceApp bindFn (nonceExprApp e)
      getBindings (AppExpr e) =
        cacheResult (ExprPPIndex (indexValue (appExprId e)))
                    (appExprLoc e)
                    (ppApp' (appExprApp e))
      getBindings (BoundVarExpr i) =
        return $ stringPPExpr $ ppBoundVar i

  r <- getBindings e0
  bindings <- toList <$> readSTRef bindingsRef
  return (toList bindings, r)



------------------------------------------------------------------------
-- ExprBoundVar

instance Eq (ExprBoundVar t tp) where
  x == y = bvarId x == bvarId y

instance TestEquality (ExprBoundVar t) where
  testEquality x y = testEquality (bvarId x) (bvarId y)

instance Ord (ExprBoundVar t tp) where
  compare x y = compare (bvarId x) (bvarId y)

instance OrdF (ExprBoundVar t) where
  compareF x y = compareF (bvarId x) (bvarId y)

instance Hashable (ExprBoundVar t tp) where
  hashWithSalt s x = hashWithSalt s (bvarId x)

instance HashableF (ExprBoundVar t) where
  hashWithSaltF = hashWithSalt

------------------------------------------------------------------------
-- ExprSymFn

instance Show (ExprSymFn t args ret) where
  show f | symFnName f == emptySymbol = "f" ++ show (indexValue (symFnId f))
         | otherwise                  = show (symFnName f)

symFnArgTypes :: ExprSymFn t args ret -> Ctx.Assignment BaseTypeRepr args
symFnArgTypes f =
  case symFnInfo f of
    UninterpFnInfo tps _ -> tps
    DefinedFnInfo vars _ _ -> fmapFC bvarType vars
    MatlabSolverFnInfo fn_id _ _ -> matlabSolverArgTypes fn_id

symFnReturnType :: ExprSymFn t args ret -> BaseTypeRepr ret
symFnReturnType f =
  case symFnInfo f of
    UninterpFnInfo _ tp -> tp
    DefinedFnInfo _ r _ -> exprType r
    MatlabSolverFnInfo fn_id _ _ -> matlabSolverReturnType fn_id

-- | Return solver function associated with ExprSymFn if any.
asMatlabSolverFn :: ExprSymFn t args ret -> Maybe (MatlabSolverFn (Expr t) args ret)
asMatlabSolverFn f
  | MatlabSolverFnInfo g _ _ <- symFnInfo f = Just g
  | otherwise = Nothing


instance Eq (ExprSymFn t args tp) where
  x == y = isJust (testExprSymFnEq x y)

instance Hashable (ExprSymFn t args tp) where
  hashWithSalt s f = s `hashWithSalt` symFnId f

testExprSymFnEq ::
  ExprSymFn t a1 r1 -> ExprSymFn t a2 r2 -> Maybe ((a1::>r1) :~: (a2::>r2))
testExprSymFnEq f g = testEquality (symFnId f) (symFnId g)


instance IsSymFn (ExprSymFn t) where
  fnArgTypes = symFnArgTypes
  fnReturnType = symFnReturnType
  fnTestEquality = testExprSymFnEq
  fnCompare f g = compareF (symFnId f) (symFnId g)


-------------------------------------------------------------------------------
-- BVOrSet

instance Semigroup (BVOrNote w) where
  BVOrNote xh xa <> BVOrNote yh ya = BVOrNote (xh <> yh) (BVD.or xa ya)

traverseBVOrSet :: (HashableF f, HasAbsValue f, OrdF f, Applicative m) =>
  (forall tp. e tp -> m (f tp)) ->
  (BVOrSet e w -> m (BVOrSet f w))
traverseBVOrSet f (BVOrSet m) =
  foldr bvOrInsert (BVOrSet AM.empty) <$> traverse (f . unWrap . fst) (AM.toList m)

bvOrInsert :: (OrdF e, HashableF e, HasAbsValue e) => e (BaseBVType w) -> BVOrSet e w -> BVOrSet e w
bvOrInsert e (BVOrSet m) = BVOrSet $ AM.insert (Wrap e) (BVOrNote (mkIncrHash (hashF e)) (getAbsValue e)) () m

bvOrSingleton :: (OrdF e, HashableF e, HasAbsValue e) => e (BaseBVType w) -> BVOrSet e w
bvOrSingleton e = bvOrInsert e (BVOrSet AM.empty)

bvOrContains :: OrdF e => e (BaseBVType w) -> BVOrSet e w -> Bool
bvOrContains x (BVOrSet m) = isJust $ AM.lookup (Wrap x) m

bvOrUnion :: OrdF e => BVOrSet e w -> BVOrSet e w -> BVOrSet e w
bvOrUnion (BVOrSet x) (BVOrSet y) = BVOrSet (AM.union x y)

bvOrToList :: BVOrSet e w -> [e (BaseBVType w)]
bvOrToList (BVOrSet m) = unWrap . fst <$> AM.toList m

bvOrAbs :: (OrdF e, 1 <= w) => NatRepr w -> BVOrSet e w -> BVD.BVDomain w
bvOrAbs w (BVOrSet m) =
  case AM.annotation m of
    Just (BVOrNote _ a) -> a
    Nothing -> BVD.singleton w 0

instance (OrdF e, TestEquality e) => Eq (BVOrSet e w) where
  BVOrSet x == BVOrSet y = AM.eqBy (\_ _ -> True) x y

instance OrdF e => Hashable (BVOrSet e w) where
  hashWithSalt s (BVOrSet m) =
    case AM.annotation m of
      Just (BVOrNote h _) -> hashWithSalt s h
      Nothing -> s

------------------------------------------------------------------------
-- Types

nonceAppType :: IsExpr e => NonceApp t e tp -> BaseTypeRepr tp
nonceAppType a =
  case a of
    Annotation tpr _ _ -> tpr
    Forall{} -> knownRepr
    Exists{} -> knownRepr
    ArrayFromFn   fn       -> BaseArrayRepr (symFnArgTypes fn) (symFnReturnType fn)
    MapOverArrays fn idx _ -> BaseArrayRepr idx (symFnReturnType fn)
    ArrayTrueOnEntries _ _ -> knownRepr
    FnApp f _ ->  symFnReturnType f

appType :: App e tp -> BaseTypeRepr tp
appType a =
  case a of
    BaseIte tp _ _ _ _ -> tp
    BaseEq{} -> knownRepr

    NotPred{} -> knownRepr
    ConjPred{} -> knownRepr

    RealIsInteger{} -> knownRepr
    BVTestBit{} -> knownRepr
    BVSlt{}   -> knownRepr
    BVUlt{}   -> knownRepr

    IntDiv{} -> knownRepr
    IntMod{} -> knownRepr
    IntAbs{} -> knownRepr
    IntDivisible{} -> knownRepr

    SemiRingLe{} -> knownRepr
    SemiRingProd pd -> SR.semiRingBase (WSum.prodRepr pd)
    SemiRingSum s -> SR.semiRingBase (WSum.sumRepr s)

    RealDiv{} -> knownRepr
    RealSqrt{} -> knownRepr

    RoundReal{} -> knownRepr
    RoundEvenReal{} -> knownRepr
    FloorReal{} -> knownRepr
    CeilReal{}  -> knownRepr

    RealSpecialFunction{} -> knownRepr

    BVUnaryTerm u  -> BaseBVRepr (UnaryBV.width u)
    BVOrBits w _ -> BaseBVRepr w
    BVConcat w _ _ -> BaseBVRepr w
    BVSelect _ n _ -> BaseBVRepr n
    BVUdiv w _ _ -> BaseBVRepr w
    BVUrem w _ _ -> BaseBVRepr w
    BVSdiv w _ _ -> BaseBVRepr w
    BVSrem w _ _ -> BaseBVRepr w
    BVShl  w _ _  -> BaseBVRepr w
    BVLshr w _ _ -> BaseBVRepr w
    BVAshr w _ _ -> BaseBVRepr w
    BVRol w _ _ -> BaseBVRepr w
    BVRor w _ _ -> BaseBVRepr w
    BVPopcount w _ -> BaseBVRepr w
    BVCountLeadingZeros w _ -> BaseBVRepr w
    BVCountTrailingZeros w _ -> BaseBVRepr w
    BVZext  w _ -> BaseBVRepr w
    BVSext  w _ -> BaseBVRepr w
    BVFill w _ -> BaseBVRepr w

    FloatNeg fpp _ -> BaseFloatRepr fpp
    FloatAbs fpp _ -> BaseFloatRepr fpp
    FloatSqrt fpp _ _ -> BaseFloatRepr fpp
    FloatAdd fpp _ _ _ -> BaseFloatRepr fpp
    FloatSub fpp _ _ _ -> BaseFloatRepr fpp
    FloatMul fpp _ _ _ -> BaseFloatRepr fpp
    FloatDiv fpp _ _ _ -> BaseFloatRepr fpp
    FloatRem fpp _ _ -> BaseFloatRepr fpp
    FloatFMA fpp _ _ _ _ -> BaseFloatRepr fpp
    FloatFpEq{} -> knownRepr
    FloatLe{} -> knownRepr
    FloatLt{} -> knownRepr
    FloatIsNaN{} -> knownRepr
    FloatIsInf{} -> knownRepr
    FloatIsZero{} -> knownRepr
    FloatIsPos{} -> knownRepr
    FloatIsNeg{} -> knownRepr
    FloatIsSubnorm{} -> knownRepr
    FloatIsNorm{} -> knownRepr
    FloatCast fpp _ _ -> BaseFloatRepr fpp
    FloatRound fpp _ _ -> BaseFloatRepr fpp
    FloatFromBinary fpp _ -> BaseFloatRepr fpp
    FloatToBinary fpp _ -> floatPrecisionToBVType fpp
    BVToFloat fpp _ _ -> BaseFloatRepr fpp
    SBVToFloat fpp _ _ -> BaseFloatRepr fpp
    RealToFloat fpp _ _ -> BaseFloatRepr fpp
    FloatToBV w _ _ -> BaseBVRepr w
    FloatToSBV w _ _ -> BaseBVRepr w
    FloatToReal{} -> knownRepr
    FloatSpecialFunction fpp _ _ -> BaseFloatRepr fpp

    ArrayMap      idx b _ _ -> BaseArrayRepr idx b
    ConstantArray idx b _   -> BaseArrayRepr idx b
    SelectArray b _ _       -> b
    UpdateArray b itp _ _ _     -> BaseArrayRepr itp b
    CopyArray w a_repr _ _ _ _ _ _ _ -> BaseArrayRepr (singleton (BaseBVRepr w)) a_repr
    SetArray w a_repr _ _ _ _ _ -> BaseArrayRepr (singleton (BaseBVRepr w)) a_repr
    EqualArrayRange _ _ _ _ _ _ _ _ _ -> knownRepr

    IntegerToReal{} -> knownRepr
    BVToInteger{} -> knownRepr
    SBVToInteger{} -> knownRepr

    IntegerToBV _ w -> BaseBVRepr w

    RealToInteger{} -> knownRepr

    Cplx{} -> knownRepr
    RealPart{} -> knownRepr
    ImagPart{} -> knownRepr

    StringContains{} -> knownRepr
    StringIsPrefixOf{} -> knownRepr
    StringIsSuffixOf{} -> knownRepr
    StringIndexOf{} -> knownRepr
    StringSubstring si _ _ _ -> BaseStringRepr si
    StringAppend si _ -> BaseStringRepr si
    StringLength{} -> knownRepr

    StructCtor flds _     -> BaseStructRepr flds
    StructField _ _ tp    -> tp


------------------------------------------------------------------------
-- abstractEval

-- | Return an unconstrained abstract value.
unconstrainedAbsValue :: BaseTypeRepr tp -> AbstractValue tp
unconstrainedAbsValue tp = withAbstractable tp (avTop tp)


-- | Return abstract domain associated with a nonce app
quantAbsEval :: IsExpr e =>
  (forall u . e u -> AbstractValue u) ->
  NonceApp t e tp ->
  AbstractValue tp
quantAbsEval f q =
  case q of
    Annotation _ _ v -> f v
    Forall _ v -> f v
    Exists _ v -> f v
    ArrayFromFn _       -> unconstrainedAbsValue (nonceAppType q)
    MapOverArrays g _ _ -> unconstrainedAbsValue tp
      where tp = symFnReturnType g
    ArrayTrueOnEntries _ a -> f a
    FnApp g _           -> unconstrainedAbsValue (symFnReturnType g)

abstractEval :: (IsExpr e, HashableF e, OrdF e) =>
  (forall u . e u -> AbstractValue u) ->
  App e tp ->
  AbstractValue tp
abstractEval f a0 = do
  case a0 of

    BaseIte tp _ _c x y -> withAbstractable tp $ avJoin tp (f x) (f y)
    BaseEq{} -> Nothing

    NotPred{} -> Nothing
    ConjPred{} -> Nothing

    SemiRingLe{} -> Nothing
    RealIsInteger{} -> Nothing
    BVTestBit{} -> Nothing
    BVSlt{} -> Nothing
    BVUlt{} -> Nothing

    ------------------------------------------------------------------------
    -- Arithmetic operations
    IntAbs x -> intAbsRange (f x)
    IntDiv x y -> intDivRange (f x) (f y)
    IntMod x y -> intModRange (f x) (f y)

    IntDivisible{} -> Nothing

    SemiRingSum s -> WSum.sumAbsValue s
    SemiRingProd pd -> WSum.prodAbsValue pd

    BVOrBits w m -> bvOrAbs w m

    RealDiv _ _ -> ravUnbounded
    RealSqrt _  -> ravUnbounded

    RealSpecialFunction fn _ ->
      case fn of
        SFn.Pi -> ravConcreteRange 3.14 3.15
        -- TODO, other constants...

        SFn.Sin -> ravConcreteRange (-1) 1
        SFn.Cos -> ravConcreteRange (-1) 1

        -- TODO, is there other interesting range information?
        _ -> ravUnbounded

    BVUnaryTerm u -> UnaryBV.domain asConstantPred u
    BVConcat _ x y -> BVD.concat (bvWidth x) (f x) (bvWidth y) (f y)

    BVSelect i n x -> BVD.select i n (f x)
    BVUdiv _ x y -> BVD.udiv (f x) (f y)
    BVUrem _ x y -> BVD.urem (f x) (f y)
    BVSdiv w x y -> BVD.sdiv w (f x) (f y)
    BVSrem w x y -> BVD.srem w (f x) (f y)

    BVShl  w x y -> BVD.shl w (f x) (f y)
    BVLshr w x y -> BVD.lshr w (f x) (f y)
    BVAshr w x y -> BVD.ashr w (f x) (f y)
    BVRol  w x y -> BVD.rol w  (f x) (f y)
    BVRor  w x y -> BVD.ror w  (f x) (f y)
    BVZext w x   -> BVD.zext (f x) w
    BVSext w x   -> BVD.sext (bvWidth x) (f x) w
    BVFill w _   -> BVD.range w (-1) 0

    BVPopcount w x -> BVD.popcnt w (f x)
    BVCountLeadingZeros w x -> BVD.clz w (f x)
    BVCountTrailingZeros w x -> BVD.ctz w (f x)

    FloatNeg{} -> ()
    FloatAbs{} -> ()
    FloatSqrt{} -> ()
    FloatAdd{} -> ()
    FloatSub{} -> ()
    FloatMul{} -> ()
    FloatDiv{} -> ()
    FloatRem{} -> ()
    FloatFMA{} -> ()
    FloatFpEq{} -> Nothing
    FloatLe{} -> Nothing
    FloatLt{} -> Nothing
    FloatIsNaN{} -> Nothing
    FloatIsInf{} -> Nothing
    FloatIsZero{} -> Nothing
    FloatIsPos{} -> Nothing
    FloatIsNeg{} -> Nothing
    FloatIsSubnorm{} -> Nothing
    FloatIsNorm{} -> Nothing
    FloatCast{} -> ()
    FloatRound{} -> ()
    FloatFromBinary{} -> ()
    FloatToBinary fpp _ -> case floatPrecisionToBVType fpp of
      BaseBVRepr w -> BVD.any w
    BVToFloat{} -> ()
    SBVToFloat{} -> ()
    RealToFloat{} -> ()
    FloatToBV w _ _ -> BVD.any w
    FloatToSBV w _ _ -> BVD.any w
    FloatToReal{} -> ravUnbounded
    FloatSpecialFunction{} -> ()

    ArrayMap _ bRepr m d ->
      withAbstractable bRepr $
      case AUM.arrayUpdateAbs m of
        Nothing -> f d
        Just a -> avJoin bRepr (f d) a
    ConstantArray _idxRepr _bRepr v -> f v

    SelectArray _bRepr a _i -> f a  -- FIXME?
    UpdateArray bRepr _ a _i v -> withAbstractable bRepr $ avJoin bRepr (f a) (f v)
    CopyArray _ a_repr dest_arr _dest_idx src_arr _src_idx _len _dest_end_idx _src_end_idx ->
      withAbstractable a_repr $ avJoin a_repr (f dest_arr) (f src_arr)
    SetArray _ a_repr arr _idx val _len _end_idx ->
      withAbstractable a_repr $ avJoin a_repr (f arr) (f val)
    EqualArrayRange{} -> Nothing

    IntegerToReal x -> RAV (mapRange toRational (f x)) (Just True)
    BVToInteger x -> valueRange (Inclusive lx) (Inclusive ux)
      where (lx, ux) = BVD.ubounds (f x)
    SBVToInteger x -> valueRange (Inclusive lx) (Inclusive ux)
      where (lx, ux) = BVD.sbounds (bvWidth x) (f x)
    RoundReal x -> mapRange roundAway (ravRange (f x))
    RoundEvenReal x -> mapRange round (ravRange (f x))
    FloorReal x -> mapRange floor (ravRange (f x))
    CeilReal x  -> mapRange ceiling (ravRange (f x))
    IntegerToBV x w -> BVD.range w l u
      where rng = f x
            l = case rangeLowBound rng of
                  Unbounded -> minUnsigned w
                  Inclusive v -> max (minUnsigned w) v
            u = case rangeHiBound rng of
                  Unbounded -> maxUnsigned w
                  Inclusive v -> min (maxUnsigned w) v
    RealToInteger x -> valueRange (ceiling <$> lx) (floor <$> ux)
      where lx = rangeLowBound rng
            ux = rangeHiBound rng
            rng = ravRange (f x)

    Cplx c -> f <$> c
    RealPart x -> realPart (f x)
    ImagPart x -> imagPart (f x)

    StringContains{} -> Nothing
    StringIsPrefixOf{} -> Nothing
    StringIsSuffixOf{} -> Nothing
    StringLength s -> stringAbsLength (f s)
    StringSubstring _ s t l -> stringAbsSubstring (f s) (f t) (f l)
    StringIndexOf s t k -> stringAbsIndexOf (f s) (f t) (f k)
    StringAppend _ xs -> SSeq.stringSeqAbs xs

    StructCtor _ flds -> fmapFC (\v -> AbstractValueWrapper (f v)) flds
    StructField s idx _ -> unwrapAV (f s Ctx.! idx)


reduceApp :: IsExprBuilder sym
          => sym
          -> (forall w. (1 <= w) => sym -> UnaryBV (Pred sym) w -> IO (SymExpr sym (BaseBVType w)))
          -> App (SymExpr sym) tp
          -> IO (SymExpr sym tp)
reduceApp sym unary a0 = do
  case a0 of
    BaseIte _ _ c x y -> baseTypeIte sym c x y
    BaseEq _ x y -> isEq sym x y

    NotPred x -> notPred sym x
    ConjPred bm ->
      case BM.viewBoolMap bm of
        BoolMapDualUnit -> return $ falsePred sym
        BoolMapUnit     -> return $ truePred sym
        BoolMapTerms tms ->
          do let pol (p, Positive) = return p
                 pol (p, Negative) = notPred sym p
             x:|xs <- mapM pol tms
             foldM (andPred sym) x xs

    SemiRingSum s ->
      case WSum.sumRepr s of
        SR.SemiRingIntegerRepr ->
          WSum.evalM (intAdd sym) (\c x -> intMul sym x =<< intLit sym c) (intLit sym) s
        SR.SemiRingRealRepr ->
          WSum.evalM (realAdd sym) (\c x -> realMul sym x =<< realLit sym c) (realLit sym) s
        SR.SemiRingBVRepr SR.BVArithRepr w ->
          WSum.evalM (bvAdd sym) (\c x -> bvMul sym x =<< bvLit sym w c) (bvLit sym w) s
        SR.SemiRingBVRepr SR.BVBitsRepr w ->
          WSum.evalM (bvXorBits sym) (\c x -> bvAndBits sym x =<< bvLit sym w c) (bvLit sym w) s

    SemiRingProd pd ->
      case WSum.prodRepr pd of
        SR.SemiRingIntegerRepr ->
          maybe (intLit sym 1) return =<< WSum.prodEvalM (intMul sym) return pd
        SR.SemiRingRealRepr ->
          maybe (realLit sym 1) return =<< WSum.prodEvalM (realMul sym) return pd
        SR.SemiRingBVRepr SR.BVArithRepr w ->
          maybe (bvLit sym w (BV.one w)) return =<< WSum.prodEvalM (bvMul sym) return pd
        SR.SemiRingBVRepr SR.BVBitsRepr w ->
          maybe (bvLit sym w (BV.maxUnsigned w)) return =<< WSum.prodEvalM (bvAndBits sym) return pd

    SemiRingLe SR.OrderedSemiRingRealRepr x y -> realLe sym x y
    SemiRingLe SR.OrderedSemiRingIntegerRepr x y -> intLe sym x y

    RealIsInteger x -> isInteger sym x

    IntDiv x y -> intDiv sym x y
    IntMod x y -> intMod sym x y
    IntAbs x -> intAbs sym x
    IntDivisible x k -> intDivisible sym x k

    RealDiv x y -> realDiv sym x y
    RealSqrt x  -> realSqrt sym x

    RealSpecialFunction fn (SFn.SpecialFnArgs args) ->
      realSpecialFunction sym fn args

    BVOrBits w bs ->
      case bvOrToList bs of
        [] -> bvLit sym w (BV.zero w)
        (x:xs) -> foldM (bvOrBits sym) x xs

    BVTestBit i e -> testBitBV sym i e
    BVSlt x y -> bvSlt sym x y
    BVUlt x y -> bvUlt sym x y
    BVUnaryTerm x -> unary sym x
    BVConcat _ x y -> bvConcat sym x y
    BVSelect idx n x -> bvSelect sym idx n x
    BVUdiv _ x y -> bvUdiv sym x y
    BVUrem _ x y -> bvUrem sym x y
    BVSdiv _ x y -> bvSdiv sym x y
    BVSrem _ x y -> bvSrem sym x y
    BVShl _ x y  -> bvShl  sym x y
    BVLshr _ x y -> bvLshr sym x y
    BVAshr _ x y -> bvAshr sym x y
    BVRol  _ x y -> bvRol sym x y
    BVRor  _ x y -> bvRor sym x y
    BVZext  w x  -> bvZext sym w x
    BVSext  w x  -> bvSext sym w x
    BVPopcount _ x -> bvPopcount sym x
    BVFill w p -> bvFill sym w p
    BVCountLeadingZeros _ x -> bvCountLeadingZeros sym x
    BVCountTrailingZeros _ x -> bvCountTrailingZeros sym x

    FloatNeg _ x -> floatNeg sym x
    FloatAbs _ x -> floatAbs sym x
    FloatSqrt _ r x -> floatSqrt sym r x
    FloatAdd _ r x y -> floatAdd sym r x y
    FloatSub _ r x y -> floatSub sym r x y
    FloatMul _ r x y -> floatMul sym r x y
    FloatDiv _ r x y -> floatDiv sym r x y
    FloatRem _ x y -> floatRem sym x y
    FloatFMA _ r x y z -> floatFMA sym r x y z
    FloatFpEq x y -> floatFpEq sym x y
    FloatLe   x y -> floatLe sym x y
    FloatLt   x y -> floatLt sym x y
    FloatIsNaN     x -> floatIsNaN sym x
    FloatIsInf     x -> floatIsInf sym x
    FloatIsZero    x -> floatIsZero sym x
    FloatIsPos     x -> floatIsPos sym x
    FloatIsNeg     x -> floatIsNeg sym x
    FloatIsSubnorm x -> floatIsSubnorm sym x
    FloatIsNorm    x -> floatIsNorm sym x
    FloatCast fpp r x -> floatCast sym fpp r x
    FloatRound  _ r x -> floatRound sym r x
    FloatFromBinary fpp x -> floatFromBinary sym fpp x
    FloatToBinary   _   x -> floatToBinary sym x
    BVToFloat   fpp r x -> bvToFloat sym fpp r x
    SBVToFloat  fpp r x -> sbvToFloat sym fpp r x
    RealToFloat fpp r x -> realToFloat sym fpp r x
    FloatToBV   w   r x -> floatToBV sym w r x
    FloatToSBV  w   r x -> floatToSBV sym w r x
    FloatToReal x -> floatToReal sym x
    FloatSpecialFunction fpp fn (SFn.SpecialFnArgs args) ->
      floatSpecialFunction sym fpp fn args

    ArrayMap _ _ m def_map ->
      arrayUpdateAtIdxLits sym m def_map
    ConstantArray idx_tp _ e -> constantArray sym idx_tp e
    SelectArray _ a i     -> arrayLookup sym a i
    UpdateArray _ _ a i v -> arrayUpdate sym a i v
    CopyArray _ _ dest_arr dest_idx src_arr src_idx len _ _ ->
      arrayCopy sym dest_arr dest_idx src_arr src_idx len
    SetArray _ _ arr idx val len _ -> arraySet sym arr idx val len
    EqualArrayRange _ _ x_arr x_idx y_arr y_idx len _ _ ->
      arrayRangeEq sym x_arr x_idx y_arr y_idx len

    IntegerToReal x -> integerToReal sym x
    RealToInteger x -> realToInteger sym x

    BVToInteger x   -> bvToInteger sym x
    SBVToInteger x  -> sbvToInteger sym x
    IntegerToBV x w -> integerToBV sym x w

    RoundReal x -> realRound sym x
    RoundEvenReal x -> realRoundEven sym x
    FloorReal x -> realFloor sym x
    CeilReal  x -> realCeil sym x

    Cplx c     -> mkComplex sym c
    RealPart x -> getRealPart sym x
    ImagPart x -> getImagPart sym x

    StringIndexOf x y k -> stringIndexOf sym x y k
    StringContains x y -> stringContains sym x y
    StringIsPrefixOf x y -> stringIsPrefixOf sym x y
    StringIsSuffixOf x y -> stringIsSuffixOf sym x y
    StringSubstring _ x off len -> stringSubstring sym x off len

    StringAppend si xs ->
       do e <- stringEmpty sym si
          let f x (SSeq.StringSeqLiteral l) = stringConcat sym x =<< stringLit sym l
              f x (SSeq.StringSeqTerm y) = stringConcat sym x y
          foldM f e (SSeq.toList xs)

    StringLength x -> stringLength sym x

    StructCtor _ args -> mkStruct sym args
    StructField s i _ -> structField sym s i

------------------------------------------------------------------------
-- App operations


ppVar :: String -> SolverSymbol -> Nonce t tp -> BaseTypeRepr tp -> String
ppVar pr sym i tp = pr ++ show sym ++ "@" ++ show (indexValue i) ++ ":" ++ ppVarTypeCode tp

ppBoundVar :: ExprBoundVar t tp -> String
ppBoundVar v =
  case bvarKind v of
    QuantifierVarKind -> ppVar "?" (bvarName v) (bvarId v) (bvarType v)
    LatchVarKind   -> ppVar "l" (bvarName v) (bvarId v) (bvarType v)
    UninterpVarKind -> ppVar "c" (bvarName v) (bvarId v) (bvarType v)

instance Show (ExprBoundVar t tp) where
  show = ppBoundVar

instance ShowF (ExprBoundVar t)


-- | Pretty print a code to identify the type of constant.
ppVarTypeCode :: BaseTypeRepr tp -> String
ppVarTypeCode tp =
  case tp of
    BaseBoolRepr    -> "b"
    BaseBVRepr _    -> "bv"
    BaseIntegerRepr -> "i"
    BaseRealRepr    -> "r"
    BaseFloatRepr _ -> "f"
    BaseStringRepr _ -> "s"
    BaseComplexRepr -> "c"
    BaseArrayRepr _ _ -> "a"
    BaseStructRepr _ -> "struct"

-- | Either a argument or text or text
data PrettyArg (e :: BaseType -> Type) where
  PrettyArg  :: e tp -> PrettyArg e
  PrettyText :: Text -> PrettyArg e
  PrettyFunc :: Text -> [PrettyArg e] -> PrettyArg e

exprPrettyArg :: e tp -> PrettyArg e
exprPrettyArg e = PrettyArg e

exprPrettyIndices :: Ctx.Assignment e ctx -> [PrettyArg e]
exprPrettyIndices = toListFC exprPrettyArg

stringPrettyArg :: String -> PrettyArg e
stringPrettyArg x = PrettyText $! Text.pack x

showPrettyArg :: Show a => a -> PrettyArg e
showPrettyArg x = stringPrettyArg $! show x

type PrettyApp e = (Text, [PrettyArg e])

prettyApp :: Text -> [PrettyArg e] -> PrettyApp e
prettyApp nm args = (nm, args)

ppNonceApp :: forall m t e tp
           . Applicative m
           => (forall ctx r . ExprSymFn t ctx r -> m (PrettyArg e))
           -> NonceApp t e tp
           -> m (PrettyApp e)
ppNonceApp ppFn a0 = do
  case a0 of
    Annotation _ n x -> pure $ prettyApp "annotation" [ showPrettyArg n, exprPrettyArg x ]
    Forall v x -> pure $ prettyApp "forall" [ stringPrettyArg (ppBoundVar v), exprPrettyArg x ]
    Exists v x -> pure $ prettyApp "exists" [ stringPrettyArg (ppBoundVar v), exprPrettyArg x ]
    ArrayFromFn f -> resolve <$> ppFn f
      where resolve f_nm = prettyApp "arrayFromFn" [ f_nm ]
    MapOverArrays f _ args -> resolve <$> ppFn f
      where resolve f_nm = prettyApp "mapArray" (f_nm : arg_nms)
            arg_nms = toListFC (\(ArrayResultWrapper a) -> exprPrettyArg a) args
    ArrayTrueOnEntries f a -> resolve <$> ppFn f
      where resolve f_nm = prettyApp "arrayTrueOnEntries" [ f_nm, a_nm ]
            a_nm = exprPrettyArg a
    FnApp f a -> resolve <$> ppFn f
      where resolve f_nm = prettyApp "apply" (f_nm : toListFC exprPrettyArg a)

instance ShowF e => Pretty (App e u) where
  pretty a = pretty nm <+> sep (ppArg <$> args)
    where (nm, args) = ppApp' a
          ppArg :: PrettyArg e -> Doc ann
          ppArg (PrettyArg e) = pretty (showF e)
          ppArg (PrettyText txt) = pretty txt
          ppArg (PrettyFunc fnm fargs) = parens (pretty fnm <+> sep (ppArg <$> fargs))

instance ShowF e => Show (App e u) where
  show = show . pretty

ppApp' :: forall e u . App e u -> PrettyApp e
ppApp' a0 = do
  let ppSExpr :: Text -> [e x] -> PrettyApp e
      ppSExpr f l = prettyApp f (exprPrettyArg <$> l)

  case a0 of
    BaseIte _ _ c x y -> prettyApp "ite" [exprPrettyArg c, exprPrettyArg x, exprPrettyArg y]
    BaseEq _ x y -> ppSExpr "eq" [x, y]

    NotPred x -> ppSExpr "not" [x]

    ConjPred xs ->
      let pol (x,Positive) = exprPrettyArg x
          pol (x,Negative) = PrettyFunc "not" [ exprPrettyArg x ]
       in
       case BM.viewBoolMap xs of
         BoolMapUnit      -> prettyApp "true" []
         BoolMapDualUnit  -> prettyApp "false" []
         BoolMapTerms tms -> prettyApp "and" (map pol (toList tms))

    RealIsInteger x -> ppSExpr "isInteger" [x]
    BVTestBit i x   -> prettyApp "testBit"  [exprPrettyArg x, showPrettyArg i]
    BVUlt x y -> ppSExpr "bvUlt" [x, y]
    BVSlt x y -> ppSExpr "bvSlt" [x, y]

    IntAbs x   -> prettyApp "intAbs" [exprPrettyArg x]
    IntDiv x y -> prettyApp "intDiv" [exprPrettyArg x, exprPrettyArg y]
    IntMod x y -> prettyApp "intMod" [exprPrettyArg x, exprPrettyArg y]
    IntDivisible x k -> prettyApp "intDivisible" [exprPrettyArg x, showPrettyArg k]

    SemiRingLe sr x y ->
      case sr of
        SR.OrderedSemiRingRealRepr    -> ppSExpr "realLe" [x, y]
        SR.OrderedSemiRingIntegerRepr -> ppSExpr "intLe" [x, y]

    SemiRingSum s ->
      case WSum.sumRepr s of
        SR.SemiRingRealRepr -> prettyApp "realSum" (WSum.eval (++) ppEntry ppConstant s)
          where ppConstant 0 = []
                ppConstant c = [ stringPrettyArg (ppRat c) ]
                ppEntry 1 e  = [ exprPrettyArg e ]
                ppEntry sm e = [ PrettyFunc "realAdd" [stringPrettyArg (ppRat sm), exprPrettyArg e ] ]
                ppRat r | d == 1 = show n
                        | otherwise = "(" ++ show n ++ "/" ++ show d ++ ")"
                     where n = numerator r
                           d = denominator r

        SR.SemiRingIntegerRepr -> prettyApp "intSum" (WSum.eval (++) ppEntry ppConstant s)
          where ppConstant 0 = []
                ppConstant c = [ stringPrettyArg (show c) ]
                ppEntry 1 e  = [ exprPrettyArg e ]
                ppEntry sm e = [ PrettyFunc "intMul" [stringPrettyArg (show sm), exprPrettyArg e ] ]

        SR.SemiRingBVRepr SR.BVArithRepr w -> prettyApp "bvSum" (WSum.eval (++) ppEntry ppConstant s)
          where ppConstant (BV.BV 0) = []
                ppConstant c = [ stringPrettyArg (ppBV c) ]
                ppEntry sm e
                  | sm == BV.one w = [ exprPrettyArg e ]
                  | otherwise = [ PrettyFunc "bvMul" [ stringPrettyArg (ppBV sm), exprPrettyArg e ] ]
                ppBV = BV.ppHex w

        SR.SemiRingBVRepr SR.BVBitsRepr w -> prettyApp "bvXor" (WSum.eval (++) ppEntry ppConstant s)
          where ppConstant (BV.BV 0) = []
                ppConstant c = [ stringPrettyArg (ppBV c) ]
                ppEntry sm e
                  | sm == BV.maxUnsigned w = [ exprPrettyArg e ]
                  | otherwise = [ PrettyFunc "bvAnd" [ stringPrettyArg (ppBV sm), exprPrettyArg e ] ]
                ppBV = BV.ppHex w

    SemiRingProd pd ->
      case WSum.prodRepr pd of
        SR.SemiRingRealRepr ->
          prettyApp "realProd" $ fromMaybe [] (WSum.prodEval (++) ((:[]) . exprPrettyArg) pd)
        SR.SemiRingIntegerRepr ->
          prettyApp "intProd" $ fromMaybe [] (WSum.prodEval (++) ((:[]) . exprPrettyArg) pd)
        SR.SemiRingBVRepr SR.BVArithRepr _w ->
          prettyApp "bvProd" $ fromMaybe [] (WSum.prodEval (++) ((:[]) . exprPrettyArg) pd)
        SR.SemiRingBVRepr SR.BVBitsRepr _w ->
          prettyApp "bvAnd" $ fromMaybe [] (WSum.prodEval (++) ((:[]) . exprPrettyArg) pd)


    RealDiv x y -> ppSExpr "divReal" [x, y]
    RealSqrt x  -> ppSExpr "sqrt" [x]

    RealSpecialFunction fn (SFn.SpecialFnArgs xs) ->
      prettyApp (Text.pack (show fn)) (toListFC (\ (SFn.SpecialFnArg x) -> exprPrettyArg x) xs)

    --------------------------------
    -- Bitvector operations

    BVUnaryTerm u -> prettyApp "bvUnary" (concatMap go $ UnaryBV.unsignedEntries u)
      where go :: (Integer, e BaseBoolType) -> [PrettyArg e]
            go (k,v) = [ exprPrettyArg v, showPrettyArg k ]
    BVOrBits _ bs -> prettyApp "bvOr" $ map exprPrettyArg $ bvOrToList bs

    BVConcat _ x y -> prettyApp "bvConcat" [exprPrettyArg x, exprPrettyArg y]
    BVSelect idx n x -> prettyApp "bvSelect" [showPrettyArg idx, showPrettyArg n, exprPrettyArg x]
    BVUdiv _ x y -> ppSExpr "bvUdiv" [x, y]
    BVUrem _ x y -> ppSExpr "bvUrem" [x, y]
    BVSdiv _ x y -> ppSExpr "bvSdiv" [x, y]
    BVSrem _ x y -> ppSExpr "bvSrem" [x, y]

    BVShl  _ x y -> ppSExpr "bvShl" [x, y]
    BVLshr _ x y -> ppSExpr "bvLshr" [x, y]
    BVAshr _ x y -> ppSExpr "bvAshr" [x, y]
    BVRol  _ x y -> ppSExpr "bvRol" [x, y]
    BVRor  _ x y -> ppSExpr "bvRor" [x, y]

    BVZext w x -> prettyApp "bvZext"   [showPrettyArg w, exprPrettyArg x]
    BVSext w x -> prettyApp "bvSext"   [showPrettyArg w, exprPrettyArg x]
    BVFill w p -> prettyApp "bvFill"   [showPrettyArg w, exprPrettyArg p]

    BVPopcount w x -> prettyApp "bvPopcount" [showPrettyArg w, exprPrettyArg x]
    BVCountLeadingZeros w x -> prettyApp "bvCountLeadingZeros" [showPrettyArg w, exprPrettyArg x]
    BVCountTrailingZeros w x -> prettyApp "bvCountTrailingZeros" [showPrettyArg w, exprPrettyArg x]

    --------------------------------
    -- Float operations

    FloatNeg _ x -> ppSExpr "floatNeg" [x]
    FloatAbs _ x -> ppSExpr "floatAbs" [x]
    FloatSqrt _ r x -> ppSExpr (Text.pack $ "floatSqrt " <> show r) [x]
    FloatAdd _ r x y -> ppSExpr (Text.pack $ "floatAdd " <> show r) [x, y]
    FloatSub _ r x y -> ppSExpr (Text.pack $ "floatSub " <> show r) [x, y]
    FloatMul _ r x y -> ppSExpr (Text.pack $ "floatMul " <> show r) [x, y]
    FloatDiv _ r x y -> ppSExpr (Text.pack $ "floatDiv " <> show r) [x, y]
    FloatRem _ x y -> ppSExpr "floatRem" [x, y]
    FloatFMA _ r x y z -> ppSExpr (Text.pack $ "floatFMA " <> show r) [x, y, z]
    FloatFpEq x y -> ppSExpr "floatFpEq" [x, y]
    FloatLe x y -> ppSExpr "floatLe" [x, y]
    FloatLt x y -> ppSExpr "floatLt" [x, y]
    FloatIsNaN x -> ppSExpr "floatIsNaN" [x]
    FloatIsInf x -> ppSExpr "floatIsInf" [x]
    FloatIsZero x -> ppSExpr "floatIsZero" [x]
    FloatIsPos x -> ppSExpr "floatIsPos" [x]
    FloatIsNeg x -> ppSExpr "floatIsNeg" [x]
    FloatIsSubnorm x -> ppSExpr "floatIsSubnorm" [x]
    FloatIsNorm x -> ppSExpr "floatIsNorm" [x]
    FloatCast _ r x -> ppSExpr (Text.pack $ "floatCast " <> show r) [x]
    FloatRound _ r x -> ppSExpr (Text.pack $ "floatRound " <> show r) [x]
    FloatFromBinary _ x -> ppSExpr "floatFromBinary" [x]
    FloatToBinary _ x -> ppSExpr "floatToBinary" [x]
    BVToFloat _ r x -> ppSExpr (Text.pack $ "bvToFloat " <> show r) [x]
    SBVToFloat _ r x -> ppSExpr (Text.pack $ "sbvToFloat " <> show r) [x]
    RealToFloat _ r x -> ppSExpr (Text.pack $ "realToFloat " <> show r) [x]
    FloatToBV _ r x -> ppSExpr (Text.pack $ "floatToBV " <> show r) [x]
    FloatToSBV _ r x -> ppSExpr (Text.pack $ "floatToSBV " <> show r) [x]
    FloatToReal x -> ppSExpr "floatToReal " [x]
    FloatSpecialFunction _fpp fn (SFn.SpecialFnArgs args) ->
      prettyApp (Text.pack (show fn)) (toListFC (\ (SFn.SpecialFnArg x) -> exprPrettyArg x) args)

    -------------------------------------
    -- Arrays

    ArrayMap _ _ m d ->
        prettyApp "arrayMap" (foldr ppEntry [exprPrettyArg d] (AUM.toList m))
      where ppEntry (k,e) l = showPrettyArg k : exprPrettyArg e : l
    ConstantArray _ _ v ->
      prettyApp "constArray" [exprPrettyArg v]
    SelectArray _ a i ->
      prettyApp "select" (exprPrettyArg a : exprPrettyIndices i)
    UpdateArray _ _ a i v ->
      prettyApp "update" ([exprPrettyArg a] ++ exprPrettyIndices i ++ [exprPrettyArg v])
    CopyArray _ _ dest_arr dest_idx src_arr src_idx len _ _ ->
      prettyApp
        "arrayCopy"
        [ exprPrettyArg dest_arr
        , exprPrettyArg dest_idx
        , exprPrettyArg src_arr
        , exprPrettyArg src_idx
        , exprPrettyArg len
        ]
    SetArray _ _ arr idx val len _ ->
      prettyApp
        "arraySet"
        [exprPrettyArg arr, exprPrettyArg idx, exprPrettyArg val, exprPrettyArg len]
    EqualArrayRange _ _ x_arr x_idx y_arr y_idx len _ _ ->
      prettyApp
        "arrayRangeEq"
        [ exprPrettyArg x_arr
        , exprPrettyArg x_idx
        , exprPrettyArg y_arr
        , exprPrettyArg y_idx
        , exprPrettyArg len
        ]

    ------------------------------------------------------------------------
    -- Conversions.

    IntegerToReal x -> ppSExpr "integerToReal" [x]
    BVToInteger  x  -> ppSExpr "bvToInteger" [x]
    SBVToInteger x  -> ppSExpr "sbvToInteger" [x]

    RoundReal x -> ppSExpr "round" [x]
    RoundEvenReal x -> ppSExpr "roundEven" [x]
    FloorReal x -> ppSExpr "floor" [x]
    CeilReal  x -> ppSExpr "ceil"  [x]

    IntegerToBV x w -> prettyApp "integerToBV" [exprPrettyArg x, showPrettyArg w]

    RealToInteger x   -> ppSExpr "realToInteger" [x]

    ------------------------------------------------------------------------
    -- String operations

    StringIndexOf x y k ->
       prettyApp "string-index-of" [exprPrettyArg x, exprPrettyArg y, exprPrettyArg k]
    StringContains x y -> ppSExpr "string-contains" [x, y]
    StringIsPrefixOf x y -> ppSExpr "string-is-prefix-of" [x, y]
    StringIsSuffixOf x y -> ppSExpr "string-is-suffix-of" [x, y]
    StringSubstring _ x off len ->
       prettyApp "string-substring" [exprPrettyArg x, exprPrettyArg off, exprPrettyArg len]
    StringAppend _ xs -> prettyApp "string-append" (map f (SSeq.toList xs))
          where f (SSeq.StringSeqLiteral l) = showPrettyArg l
                f (SSeq.StringSeqTerm t)    = exprPrettyArg t
    StringLength x -> ppSExpr "string-length" [x]

    ------------------------------------------------------------------------
    -- Complex operations

    Cplx (r :+ i) -> ppSExpr "complex" [r, i]
    RealPart x -> ppSExpr "realPart" [x]
    ImagPart x -> ppSExpr "imagPart" [x]

    ------------------------------------------------------------------------
    -- SymStruct

    StructCtor _ flds -> prettyApp "struct" (toListFC exprPrettyArg flds)
    StructField s idx _ ->
      prettyApp "field" [exprPrettyArg s, showPrettyArg idx]

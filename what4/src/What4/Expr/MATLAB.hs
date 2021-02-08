{-|
Module      : What4.Expr.MATLAB
Description : Low-level support for MATLAB-style arithmetic operations
Copyright   : (c) Galois, Inc, 2016-2020
License     : BSD3
Maintainer  : Joe Hendrix <jhendrix@galois.com>

This module provides an interface that a symbolic backend should
implement to support MATLAB intrinsics.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
module What4.Expr.MATLAB
  ( MatlabSolverFn(..)
  , matlabSolverArgTypes
  , matlabSolverReturnType
  , ppMatlabSolverFn
  , evalMatlabSolverFn
  , testSolverFnEq
  , traverseMatlabSolverFn
  , MatlabSymbolicArrayBuilder(..)

    -- * Utilities for definition
  , clampedIntAdd
  , clampedIntSub
  , clampedIntMul
  , clampedIntNeg
  , clampedIntAbs
  , clampedUIntAdd
  , clampedUIntSub
  , clampedUIntMul
  ) where

import           Control.Monad (join)
import qualified Data.BitVector.Sized as BV
import           Data.Kind (Type)
import           Data.Hashable
import           Data.Parameterized.Classes
import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.TH.GADT
import           Data.Parameterized.TraversableFC
import           Prettyprinter

import           What4.BaseTypes
import           What4.Interface
import           What4.Utils.Complex
import           What4.Utils.OnlyIntRepr

------------------------------------------------------------------------
-- MatlabSolverFn


clampedIntAdd :: (IsExprBuilder sym, 1 <= w)
              => sym
              -> SymBV sym w
              -> SymBV sym w
              -> IO (SymBV sym w)
clampedIntAdd sym x y = do
  let w = bvWidth x
  withAddPrefixLeq w (knownNat :: NatRepr 1) $ do
  -- Compute result with 1 additional bit to catch clamping
  let w' = incNat w
  x'  <- bvSext sym w' x
  y'  <- bvSext sym w' y
  -- Compute result.
  r'  <- bvAdd sym x' y'

  -- Check is result is greater than or equal to max value.
  too_high <- bvSgt sym r' =<< bvLit sym w' (BV.maxSigned w')
  max_int <- bvLit sym w (BV.maxSigned w)

  -- Check is result is less than min value.
  too_low <- bvSlt sym r' =<< bvLit sym w' (BV.minSigned w')
  min_int <- bvLit sym w (BV.minSigned w)

  -- Clamp integer range.
  r <- bvTrunc sym w r'
  r_low <- bvIte sym too_low min_int r
  bvIte sym too_high max_int r_low

clampedIntSub :: (IsExprBuilder sym, 1 <= w)
              => sym
              -> SymBV sym w
              -> SymBV sym w
              -> IO (SymBV sym w)
clampedIntSub sym x y = do
  let w = bvWidth x
  (ov, xy) <- subSignedOF sym x y
  ysign  <- bvIsNeg sym y
  minint <- minSignedBV sym w
  maxint <- maxSignedBV sym w
  ov_val <- bvIte sym ysign maxint minint
  bvIte sym ov ov_val xy

clampedIntMul :: (IsExprBuilder sym, 1 <= w)
              => sym
              -> SymBV sym w
              -> SymBV sym w
              -> IO (SymBV sym w)
clampedIntMul sym x y = do
  let w = bvWidth x
  (hi,lo) <- signedWideMultiplyBV sym x y
  zro    <- bvLit sym w (BV.zero w)
  ones   <- maxUnsignedBV sym w
  ok_pos <- join $ andPred sym <$> (notPred sym =<< bvIsNeg sym lo)
                              <*> bvEq sym hi zro
  ok_neg <- join $ andPred sym <$> bvIsNeg sym lo
                              <*> bvEq sym hi ones
  ov     <- notPred sym =<< orPred sym ok_pos ok_neg

  minint <- minSignedBV sym w
  maxint <- maxSignedBV sym w
  hisign <- bvIsNeg sym hi
  ov_val <- bvIte sym hisign minint maxint
  bvIte sym ov ov_val lo


-- | Compute the clamped negation of a signed bitvector.
--
--   The only difference between this operation and the usual
--   2's complement negation function is the handling of MIN_INT.
--   The usual 2's complement negation sends MIN_INT to MIN_INT;
--   however, the clamped version instead sends MIN_INT to MAX_INT.
clampedIntNeg :: (IsExprBuilder sym, 1 <= w)
              => sym
              -> SymBV sym w
              -> IO (SymBV sym w)
clampedIntNeg sym x = do
  let w = bvWidth x
  minint <- minSignedBV sym w

  -- return maxint when x == minint, and neg(x) otherwise
  p <- bvEq sym x minint
  iteM bvIte sym p (maxSignedBV sym w) (bvNeg sym x)

-- | Compute the clamped absolute value of a signed bitvector.
--
--   The only difference between this operation and the usual 2's
--   complement operation is the handling of MIN_INT.  The usual 2's
--   complement absolute value function sends MIN_INT to MIN_INT;
--   however, the clamped version instead sends MIN_INT to MAX_INT.
clampedIntAbs :: (IsExprBuilder sym, 1 <= w)
              => sym
              -> SymBV sym w
              -> IO (SymBV sym w)
clampedIntAbs sym x = do
  isNeg  <- bvIsNeg sym x
  iteM bvIte sym isNeg (clampedIntNeg sym x) (pure x)


clampedUIntAdd :: (IsExprBuilder sym, 1 <= w)
               => sym
               -> SymBV sym w
               -> SymBV sym w
               -> IO (SymBV sym w)
clampedUIntAdd sym x y = do
  let w = bvWidth x
  (ov, xy) <- addUnsignedOF sym x y
  maxint   <- maxUnsignedBV sym w
  bvIte sym ov maxint xy

clampedUIntSub :: (IsExprBuilder sym, 1 <= w)
               => sym
               -> SymBV sym w
               -> SymBV sym w
               -> IO (SymBV sym w)
clampedUIntSub sym x y = do
  let w = bvWidth x
  no_underflow <- bvUge sym x y

  iteM bvIte
       sym
       no_underflow
       (bvSub sym x y) -- Perform subtraction if y >= x
       (bvLit sym w (BV.zero w)) -- Otherwise return min int

clampedUIntMul :: (IsExprBuilder sym, 1 <= w)
               => sym
               -> SymBV sym w
               -> SymBV sym w
               -> IO (SymBV sym w)
clampedUIntMul sym x y = do
  let w = bvWidth x
  (hi, lo) <- unsignedWideMultiplyBV sym x y
  maxint   <- maxUnsignedBV sym w
  ov       <- bvIsNonzero sym hi
  bvIte sym ov maxint lo

------------------------------------------------------------------------
-- MatlabSolverFn

-- | Builtin functions that can be used to generate symbolic functions.
--
-- These functions are expected to be total, but the value returned may not be
-- specified.  e.g. 'IntegerToNatFn' must return some natural number for every
-- integer, but for negative integers, the particular number is unspecified.
data MatlabSolverFn (f :: BaseType -> Type) args ret where

  -- Or two Boolean variables
  BoolOrFn :: MatlabSolverFn f (EmptyCtx ::> BaseBoolType ::> BaseBoolType) BaseBoolType

  -- Returns true if the real value is an integer.
  IsIntegerFn :: MatlabSolverFn f (EmptyCtx ::> BaseRealType) BaseBoolType

  -- Return true if first value is less than or equal to second.
  IntLeFn :: MatlabSolverFn f (EmptyCtx ::> BaseIntegerType ::> BaseIntegerType) BaseBoolType

  -- A function for mapping a unsigned bitvector to an integer.
  BVToIntegerFn :: (1 <= w)
            => !(NatRepr w)
            ->  MatlabSolverFn f (EmptyCtx ::> BaseBVType w) BaseIntegerType
  -- A function for mapping a signed bitvector to a integer.
  SBVToIntegerFn :: (1 <= w)
                 => !(NatRepr w)
                 -> MatlabSolverFn f (EmptyCtx ::> BaseBVType w) BaseIntegerType

  -- A function for mapping an integer to equivalent real.
  IntegerToRealFn :: MatlabSolverFn f (EmptyCtx ::> BaseIntegerType) BaseRealType

  -- A function for mapping a real to equivalent integer.
  --
  -- Function may return any value if input is not an integer.
  RealToIntegerFn :: MatlabSolverFn f (EmptyCtx ::> BaseRealType) BaseIntegerType

  -- A function that maps Booleans logical value to an integer
  -- (either 0 for false, or 1 for true)
  PredToIntegerFn :: MatlabSolverFn f (EmptyCtx ::> BaseBoolType) BaseIntegerType

  -- 'IntSeqFn base c' denotes the function '\i _ -> base + c*i
  IntSeqFn :: !(f BaseIntegerType)
           -> !(f BaseIntegerType)
           -> MatlabSolverFn f (EmptyCtx ::> BaseIntegerType ::> BaseIntegerType) BaseIntegerType

  -- 'RealSeqFn base c' denotes the function '\_ i -> base + c*i
  RealSeqFn :: !(f BaseRealType)
            -> !(f BaseRealType)
            -> MatlabSolverFn f (EmptyCtx ::> BaseIntegerType ::> BaseIntegerType) BaseRealType

  -- 'IndicesInRange tps upper_bounds' returns a predicate that is true if all the arguments
  -- (which must be natural numbers) are between 1 and the given upper bounds (inclusive).
  IndicesInRange :: !(Assignment OnlyIntRepr (idx ::> itp))
                 -> !(Assignment f (idx ::> itp))
                    -- Upper bounds on indices
                 -> MatlabSolverFn f (idx ::> itp) BaseBoolType

  IsEqFn :: !(BaseTypeRepr tp)
         -> MatlabSolverFn f (EmptyCtx ::> tp ::> tp) BaseBoolType

  ------------------------------------------------------------------------
  -- Bitvector functions

  -- Returns true if the bitvector is non-zero.
  BVIsNonZeroFn :: (1 <= w)
                => !(NatRepr w)
                -> MatlabSolverFn f (EmptyCtx ::> BaseBVType w) BaseBoolType

  -- Negate a signed bitvector
  ClampedIntNegFn :: (1 <= w)
           => !(NatRepr w)
           -> MatlabSolverFn f (EmptyCtx ::> BaseBVType w) (BaseBVType w)

  -- Get absolute value of a signed bitvector
  ClampedIntAbsFn :: (1 <= w)
         => !(NatRepr w)
         -> MatlabSolverFn f (EmptyCtx ::> BaseBVType w) (BaseBVType w)

  -- Add two values without wrapping but rather rounding to
  -- 0/max value when the result is out of range.
  ClampedIntAddFn :: (1 <= w)
           => !(NatRepr w)
           -> MatlabSolverFn f
                 (EmptyCtx ::> BaseBVType w ::> BaseBVType w)
                 (BaseBVType w)

  -- Subtract one value from another without wrapping but rather rounding to
  -- 0/max value when the result is out of range.
  ClampedIntSubFn :: (1 <= w)
           => !(NatRepr w)
           -> MatlabSolverFn f
                 (EmptyCtx ::> BaseBVType w ::> BaseBVType w)
                 (BaseBVType w)

  -- Multiple two values without wrapping but rather rounding to
  -- 0/max value when the result is out of range.
  ClampedIntMulFn :: (1 <= w)
           => !(NatRepr w)
           -> MatlabSolverFn f
                 (EmptyCtx ::> BaseBVType w ::> BaseBVType w)
                 (BaseBVType w)

  -- Add two values without wrapping but rather rounding to
  -- 0/max value when the result is out of range.
  ClampedUIntAddFn :: (1 <= w)
           => !(NatRepr w)
           -> MatlabSolverFn f
                 (EmptyCtx ::> BaseBVType w ::> BaseBVType w)
                 (BaseBVType w)

  -- Subtract one value from another without wrapping but rather rounding to
  -- 0/max value when the result is out of range.
  ClampedUIntSubFn :: (1 <= w)
           => !(NatRepr w)
           -> MatlabSolverFn f
                 (EmptyCtx ::> BaseBVType w ::> BaseBVType w)
                 (BaseBVType w)

  -- Multiple two values without wrapping but rather rounding to
  -- 0/max value when the result is out of range.
  ClampedUIntMulFn :: (1 <= w)
           => !(NatRepr w)
           -> MatlabSolverFn f
                 (EmptyCtx ::> BaseBVType w ::> BaseBVType w)
                 (BaseBVType w)

  -- Convert a signed integer to the nearest signed integer with the
  -- given width.  This clamps the value to min-int or max int when truncated
  -- the width.
  IntSetWidthFn :: (1 <= m, 1 <= n)
                => !(NatRepr m)
                -> !(NatRepr n)
                -> MatlabSolverFn f (EmptyCtx ::> BaseBVType m) (BaseBVType n)

  -- Convert a unsigned integer to the nearest unsigned integer with the
  -- given width.  This clamps the value to min-int or max int when truncated
  -- the width.
  UIntSetWidthFn :: (1 <= m, 1 <= n)
                 => !(NatRepr m)
                 -> !(NatRepr n)
                 -> MatlabSolverFn f (EmptyCtx ::> BaseBVType m) (BaseBVType n)

  -- Convert a unsigned integer to the nearest signed integer with the
  -- given width.  This clamps the value to min-int or max int when truncated
  -- the width.
  UIntToIntFn :: (1 <= m, 1 <= n)
                => !(NatRepr m)
                -> !(NatRepr n)
                -> MatlabSolverFn f (EmptyCtx ::> BaseBVType m) (BaseBVType n)

  -- Convert a signed integer to the nearest unsigned integer with the
  -- given width.  This clamps the value to min-int or max int when truncated
  -- the width.
  IntToUIntFn :: (1 <= m, 1 <= n)
              => !(NatRepr m)
              -> !(NatRepr n)
              -> MatlabSolverFn f (EmptyCtx ::> BaseBVType m) (BaseBVType n)

  ------------------------------------------------------------------------
  -- Real functions

  -- Returns true if the complex number is non-zero.
  RealIsNonZeroFn :: MatlabSolverFn f (EmptyCtx ::> BaseRealType) BaseBoolType

  RealCosFn :: MatlabSolverFn f (EmptyCtx ::> BaseRealType) BaseRealType
  RealSinFn :: MatlabSolverFn f (EmptyCtx ::> BaseRealType) BaseRealType

  ------------------------------------------------------------------------
  -- Conversion functions

  RealToSBVFn :: (1 <= w)
              => !(NatRepr w)
              -> MatlabSolverFn f (EmptyCtx ::> BaseRealType) (BaseBVType w)

  RealToUBVFn :: (1 <= w)
              => !(NatRepr w)
              -> MatlabSolverFn f (EmptyCtx ::> BaseRealType) (BaseBVType w)

  -- Return 1 if the predicate is true; 0 otherwise.
  PredToBVFn :: (1 <= w)
             => !(NatRepr w)
             -> MatlabSolverFn f (EmptyCtx ::> BaseBoolType) (BaseBVType w)

  ------------------------------------------------------------------------
  -- Complex functions

  -- Returns true if the complex number is non-zero.
  CplxIsNonZeroFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseBoolType

  -- Returns true if the imaginary part of complex number is zero.
  CplxIsRealFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseBoolType

  -- A function for mapping a real to equivalent complex with imaginary number equals 0.
  RealToComplexFn :: MatlabSolverFn f (EmptyCtx ::> BaseRealType) BaseComplexType
  -- Returns the real component out of a complex number.
  RealPartOfCplxFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseRealType
  -- Returns the imag component out of a complex number.
  ImagPartOfCplxFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseRealType

  -- Return the complex number formed by negating both components.
  CplxNegFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseComplexType

  -- Add two complex values.
  CplxAddFn :: MatlabSolverFn f
                 (EmptyCtx ::> BaseComplexType ::> BaseComplexType)
                 BaseComplexType

  -- Subtract one complex value from another.
  CplxSubFn :: MatlabSolverFn f
                 (EmptyCtx ::> BaseComplexType ::> BaseComplexType)
                 BaseComplexType

  -- Multiply two complex values.
  CplxMulFn :: MatlabSolverFn f
                 (EmptyCtx ::> BaseComplexType ::> BaseComplexType)
                 BaseComplexType

  -- Return the complex number formed by rounding both components.
  --
  -- Rounding is away from zero.
  CplxRoundFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseComplexType
  -- Return the complex number formed by taking floor of both components.
  CplxFloorFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseComplexType
  -- Return the complex number formed by taking ceiling of both components.
  CplxCeilFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseComplexType

  -- Return magningture of complex number.
  CplxMagFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseRealType

  -- Return the principal square root of a complex number.
  CplxSqrtFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseComplexType

  -- Returns complex exponential of input
  CplxExpFn :: MatlabSolverFn f
                 (EmptyCtx ::> BaseComplexType)
                 BaseComplexType
  -- Returns complex natural logarithm of input
  CplxLogFn :: MatlabSolverFn f
                 (EmptyCtx ::> BaseComplexType)
                 BaseComplexType
  -- Returns complex natural logarithm of input
  CplxLogBaseFn :: !Integer
                -> MatlabSolverFn f
                     (EmptyCtx ::> BaseComplexType)
                     BaseComplexType
  -- Returns complex sine of input
  CplxSinFn :: MatlabSolverFn f
                 (EmptyCtx ::> BaseComplexType)
                 BaseComplexType
  -- Returns complex cosine of input
  CplxCosFn :: MatlabSolverFn f
                 (EmptyCtx ::> BaseComplexType)
                 BaseComplexType
  -- Returns tangent of input.
  --
  CplxTanFn :: MatlabSolverFn f
                 (EmptyCtx ::> BaseComplexType)
                 BaseComplexType

-- Dummy declaration splice to bring App into template haskell scope.
$(return [])

traverseMatlabSolverFn :: Applicative m
                       => (forall tp . e tp -> m (f tp))
                       -> MatlabSolverFn e a r
                       -> m (MatlabSolverFn f a r)
traverseMatlabSolverFn f fn_id =
  case fn_id of
    BoolOrFn             -> pure $ BoolOrFn
    IsIntegerFn          -> pure $ IsIntegerFn
    IntLeFn              -> pure $ IntLeFn
    BVToIntegerFn w      -> pure $ BVToIntegerFn w
    SBVToIntegerFn w     -> pure $ SBVToIntegerFn w
    IntegerToRealFn      -> pure $ IntegerToRealFn
    RealToIntegerFn      -> pure $ RealToIntegerFn
    PredToIntegerFn      -> pure $ PredToIntegerFn
    IntSeqFn  b i        -> IntSeqFn <$> f b <*> f i
    RealSeqFn b i        -> RealSeqFn <$> f b <*> f i
    IndicesInRange tps a -> IndicesInRange tps <$> traverseFC f a
    IsEqFn tp            -> pure $ IsEqFn tp

    BVIsNonZeroFn w      -> pure $ BVIsNonZeroFn w

    ClampedIntNegFn w    -> pure $ ClampedIntNegFn w
    ClampedIntAbsFn w    -> pure $ ClampedIntAbsFn w
    ClampedIntAddFn w    -> pure $ ClampedIntAddFn w
    ClampedIntSubFn w    -> pure $ ClampedIntSubFn w
    ClampedIntMulFn w    -> pure $ ClampedIntMulFn w

    ClampedUIntAddFn w   -> pure $ ClampedUIntAddFn w
    ClampedUIntSubFn w   -> pure $ ClampedUIntSubFn w
    ClampedUIntMulFn w   -> pure $ ClampedUIntMulFn w

    IntSetWidthFn i o    -> pure $ IntSetWidthFn i o
    UIntSetWidthFn i o   -> pure $ UIntSetWidthFn i o
    UIntToIntFn i o      -> pure $ UIntToIntFn i o
    IntToUIntFn i o      -> pure $ IntToUIntFn i o

    RealCosFn            -> pure $ RealCosFn
    RealSinFn            -> pure $ RealSinFn
    RealIsNonZeroFn      -> pure $ RealIsNonZeroFn

    RealToSBVFn w        -> pure $ RealToSBVFn w
    RealToUBVFn w        -> pure $ RealToUBVFn w
    PredToBVFn  w        -> pure $ PredToBVFn  w


    CplxIsNonZeroFn      -> pure $ CplxIsNonZeroFn
    CplxIsRealFn         -> pure $ CplxIsRealFn
    RealToComplexFn      -> pure $ RealToComplexFn
    RealPartOfCplxFn     -> pure $ RealPartOfCplxFn
    ImagPartOfCplxFn     -> pure $ ImagPartOfCplxFn
    CplxNegFn            -> pure $ CplxNegFn
    CplxAddFn            -> pure $ CplxAddFn
    CplxSubFn            -> pure $ CplxSubFn
    CplxMulFn            -> pure $ CplxMulFn
    CplxRoundFn          -> pure $ CplxRoundFn
    CplxFloorFn          -> pure $ CplxFloorFn
    CplxCeilFn           -> pure $ CplxCeilFn
    CplxMagFn            -> pure $ CplxMagFn
    CplxSqrtFn           -> pure $ CplxSqrtFn
    CplxExpFn            -> pure $ CplxExpFn
    CplxLogFn            -> pure $ CplxLogFn
    CplxLogBaseFn b      -> pure $ CplxLogBaseFn b
    CplxSinFn            -> pure $ CplxSinFn
    CplxCosFn            -> pure $ CplxCosFn
    CplxTanFn            -> pure $ CplxTanFn

-- | Utilities to make a pair with the same value.
binCtx :: BaseTypeRepr tp -> Ctx.Assignment BaseTypeRepr (EmptyCtx ::> tp ::> tp)
binCtx tp = Ctx.empty Ctx.:> tp Ctx.:> tp

-- | Get arg tpyes of solver fn.
matlabSolverArgTypes :: MatlabSolverFn f args ret -> Assignment BaseTypeRepr args
matlabSolverArgTypes f =
  case f of
    BoolOrFn             -> knownRepr
    IsIntegerFn          -> knownRepr
    IntLeFn              -> knownRepr
    BVToIntegerFn w      -> Ctx.singleton (BaseBVRepr w)
    SBVToIntegerFn w     -> Ctx.singleton (BaseBVRepr w)
    IntegerToRealFn      -> knownRepr
    RealToIntegerFn      -> knownRepr
    PredToIntegerFn      -> knownRepr
    IntSeqFn{}           -> knownRepr
    IndicesInRange tps _ -> fmapFC toBaseTypeRepr tps
    RealSeqFn _ _        -> knownRepr
    IsEqFn tp            -> binCtx tp

    BVIsNonZeroFn w      -> Ctx.singleton (BaseBVRepr w)
    ClampedIntNegFn w    -> Ctx.singleton (BaseBVRepr w)
    ClampedIntAbsFn w    -> Ctx.singleton (BaseBVRepr w)
    ClampedIntAddFn w    -> binCtx (BaseBVRepr w)
    ClampedIntSubFn w    -> binCtx (BaseBVRepr w)
    ClampedIntMulFn w    -> binCtx (BaseBVRepr w)
    ClampedUIntAddFn w   -> binCtx (BaseBVRepr w)
    ClampedUIntSubFn w   -> binCtx (BaseBVRepr w)
    ClampedUIntMulFn w   -> binCtx (BaseBVRepr w)
    IntSetWidthFn  i _   -> Ctx.singleton (BaseBVRepr i)
    UIntSetWidthFn i _   -> Ctx.singleton (BaseBVRepr i)
    UIntToIntFn i _      -> Ctx.singleton (BaseBVRepr i)
    IntToUIntFn i _      -> Ctx.singleton (BaseBVRepr i)

    RealCosFn            -> knownRepr
    RealSinFn            -> knownRepr
    RealIsNonZeroFn      -> knownRepr

    RealToSBVFn _        -> knownRepr
    RealToUBVFn _        -> knownRepr
    PredToBVFn  _        -> knownRepr

    CplxIsNonZeroFn      -> knownRepr
    CplxIsRealFn         -> knownRepr
    RealToComplexFn      -> knownRepr
    RealPartOfCplxFn     -> knownRepr
    ImagPartOfCplxFn     -> knownRepr
    CplxNegFn            -> knownRepr
    CplxAddFn            -> knownRepr
    CplxSubFn            -> knownRepr
    CplxMulFn            -> knownRepr
    CplxRoundFn          -> knownRepr
    CplxFloorFn          -> knownRepr
    CplxCeilFn           -> knownRepr
    CplxMagFn            -> knownRepr
    CplxSqrtFn           -> knownRepr
    CplxExpFn            -> knownRepr
    CplxLogFn            -> knownRepr
    CplxLogBaseFn _      -> knownRepr
    CplxSinFn            -> knownRepr
    CplxCosFn            -> knownRepr
    CplxTanFn            -> knownRepr

-- | Get return type of solver fn.
matlabSolverReturnType :: MatlabSolverFn f args ret -> BaseTypeRepr ret
matlabSolverReturnType f =
  case f of
    BoolOrFn             -> knownRepr
    IsIntegerFn          -> knownRepr
    IntLeFn              -> knownRepr
    BVToIntegerFn{}      -> knownRepr
    SBVToIntegerFn{}     -> knownRepr
    IntegerToRealFn      -> knownRepr
    RealToIntegerFn      -> knownRepr
    PredToIntegerFn      -> knownRepr
    IntSeqFn{}           -> knownRepr
    IndicesInRange{}     -> knownRepr
    RealSeqFn _ _        -> knownRepr
    IsEqFn{}             -> knownRepr

    BVIsNonZeroFn _      -> knownRepr
    ClampedIntNegFn w    -> BaseBVRepr w
    ClampedIntAbsFn w    -> BaseBVRepr w
    ClampedIntAddFn w    -> BaseBVRepr w
    ClampedIntSubFn w    -> BaseBVRepr w
    ClampedIntMulFn w    -> BaseBVRepr w
    ClampedUIntAddFn w   -> BaseBVRepr w
    ClampedUIntSubFn w   -> BaseBVRepr w
    ClampedUIntMulFn w   -> BaseBVRepr w
    IntSetWidthFn  _ o   -> BaseBVRepr o
    UIntSetWidthFn _ o   -> BaseBVRepr o
    UIntToIntFn _ o      -> BaseBVRepr o
    IntToUIntFn _ o      -> BaseBVRepr o

    RealCosFn            -> knownRepr
    RealSinFn            -> knownRepr
    RealIsNonZeroFn      -> knownRepr

    RealToSBVFn w        -> BaseBVRepr w
    RealToUBVFn w        -> BaseBVRepr w
    PredToBVFn  w        -> BaseBVRepr w

    CplxIsNonZeroFn      -> knownRepr
    CplxIsRealFn         -> knownRepr
    RealToComplexFn      -> knownRepr
    RealPartOfCplxFn     -> knownRepr
    ImagPartOfCplxFn     -> knownRepr
    CplxNegFn            -> knownRepr
    CplxAddFn            -> knownRepr
    CplxSubFn            -> knownRepr
    CplxMulFn            -> knownRepr
    CplxRoundFn          -> knownRepr
    CplxFloorFn          -> knownRepr
    CplxCeilFn           -> knownRepr
    CplxMagFn            -> knownRepr
    CplxSqrtFn           -> knownRepr
    CplxExpFn            -> knownRepr
    CplxLogFn            -> knownRepr
    CplxLogBaseFn _      -> knownRepr
    CplxSinFn            -> knownRepr
    CplxCosFn            -> knownRepr
    CplxTanFn            -> knownRepr

ppMatlabSolverFn :: IsExpr f => MatlabSolverFn f a r -> Doc ann
ppMatlabSolverFn f =
  case f of
    BoolOrFn             -> pretty "bool_or"
    IsIntegerFn          -> pretty "is_integer"
    IntLeFn              -> pretty "int_le"
    BVToIntegerFn w      -> parens $ pretty "bv_to_int" <+> ppNatRepr w
    SBVToIntegerFn w     -> parens $ pretty "sbv_to_int" <+> ppNatRepr w
    IntegerToRealFn      -> pretty "integer_to_real"
    RealToIntegerFn      -> pretty "real_to_integer"
    PredToIntegerFn      -> pretty "pred_to_integer"
    IntSeqFn  b i        -> parens $ pretty "nat_seq"  <+> printSymExpr b <+> printSymExpr i
    RealSeqFn b i        -> parens $ pretty "real_seq" <+> printSymExpr b <+> printSymExpr i
    IndicesInRange _ bnds ->
      parens (pretty "indices_in_range" <+> sep (toListFC printSymExpr bnds))
    IsEqFn{}             -> pretty "is_eq"

    BVIsNonZeroFn w      -> parens $ pretty "bv_is_nonzero" <+> ppNatRepr w
    ClampedIntNegFn w    -> parens $ pretty "clamped_int_neg" <+> ppNatRepr w
    ClampedIntAbsFn w    -> parens $ pretty "clamped_neg_abs" <+> ppNatRepr w
    ClampedIntAddFn w    -> parens $ pretty "clamped_int_add" <+> ppNatRepr w
    ClampedIntSubFn w    -> parens $ pretty "clamped_int_sub" <+> ppNatRepr w
    ClampedIntMulFn w    -> parens $ pretty "clamped_int_mul" <+> ppNatRepr w
    ClampedUIntAddFn w   -> parens $ pretty "clamped_uint_add" <+> ppNatRepr w
    ClampedUIntSubFn w   -> parens $ pretty "clamped_uint_sub" <+> ppNatRepr w
    ClampedUIntMulFn w   -> parens $ pretty "clamped_uint_mul" <+> ppNatRepr w

    IntSetWidthFn i o    -> parens $ pretty "int_set_width"  <+> ppNatRepr i <+> ppNatRepr o
    UIntSetWidthFn i o   -> parens $ pretty "uint_set_width" <+> ppNatRepr i <+> ppNatRepr o
    UIntToIntFn i o      -> parens $ pretty "uint_to_int"  <+> ppNatRepr i <+> ppNatRepr o
    IntToUIntFn i o      -> parens $ pretty "int_to_uint"  <+> ppNatRepr i <+> ppNatRepr o

    RealCosFn            -> pretty "real_cos"
    RealSinFn            -> pretty "real_sin"
    RealIsNonZeroFn      -> pretty "real_is_nonzero"

    RealToSBVFn w        -> parens $ pretty "real_to_sbv" <+> ppNatRepr w
    RealToUBVFn w        -> parens $ pretty "real_to_sbv" <+> ppNatRepr w
    PredToBVFn  w        -> parens $ pretty "pred_to_bv"  <+> ppNatRepr w

    CplxIsNonZeroFn      -> pretty "cplx_is_nonzero"
    CplxIsRealFn         -> pretty "cplx_is_real"
    RealToComplexFn      -> pretty "real_to_complex"
    RealPartOfCplxFn     -> pretty "real_part_of_complex"
    ImagPartOfCplxFn     -> pretty "imag_part_of_complex"

    CplxNegFn            -> pretty "cplx_neg"
    CplxAddFn            -> pretty "cplx_add"
    CplxSubFn            -> pretty "cplx_sub"
    CplxMulFn            -> pretty "cplx_mul"

    CplxRoundFn          -> pretty "cplx_round"
    CplxFloorFn          -> pretty "cplx_floor"
    CplxCeilFn           -> pretty "cplx_ceil"
    CplxMagFn            -> pretty "cplx_mag"
    CplxSqrtFn           -> pretty "cplx_sqrt"
    CplxExpFn            -> pretty "cplx_exp"
    CplxLogFn            -> pretty "cplx_log"
    CplxLogBaseFn b      -> parens $ pretty "cplx_log_base" <+> pretty b
    CplxSinFn            -> pretty "cplx_sin"
    CplxCosFn            -> pretty "cplx_cos"
    CplxTanFn            -> pretty "cplx_tan"

ppNatRepr :: NatRepr w -> Doc ann
ppNatRepr = viaShow

-- | Test 'MatlabSolverFn' values for equality.
testSolverFnEq :: TestEquality f
               => MatlabSolverFn f ax rx
               -> MatlabSolverFn f ay ry
               -> Maybe ((ax ::> rx) :~: (ay ::> ry))
testSolverFnEq = $(structuralTypeEquality [t|MatlabSolverFn|]
                   [ ( DataArg 0 `TypeApp` AnyType
                     , [|testEquality|]
                     )
                   , ( ConType [t|NatRepr|] `TypeApp` AnyType
                     , [|testEquality|]
                     )
                   , ( ConType [t|Assignment|] `TypeApp` AnyType `TypeApp` AnyType
                     , [|testEquality|]
                     )
                   , ( ConType [t|BaseTypeRepr|] `TypeApp` AnyType
                     , [|testEquality|]
                     )
                   ]
                  )

instance ( Hashable (f BaseRealType)
         , Hashable (f BaseIntegerType)
         , HashableF f
         )
         => Hashable (MatlabSolverFn f args tp) where
  hashWithSalt = $(structuralHashWithSalt [t|MatlabSolverFn|] [])

realIsNonZero :: IsExprBuilder sym => sym -> SymReal sym -> IO (Pred sym)
realIsNonZero sym = realNe sym (realZero sym)

evalMatlabSolverFn :: forall sym args ret
                   .  IsExprBuilder sym
                   => MatlabSolverFn (SymExpr sym) args ret
                   -> sym
                   -> Assignment (SymExpr sym) args
                   -> IO (SymExpr sym ret)
evalMatlabSolverFn f sym =
  case f of
    BoolOrFn         -> uncurryAssignment $ orPred sym

    IsIntegerFn      -> uncurryAssignment $ isInteger sym
    IntLeFn          -> uncurryAssignment $ intLe sym
    BVToIntegerFn{}  -> uncurryAssignment $ bvToInteger sym
    SBVToIntegerFn{} -> uncurryAssignment $ sbvToInteger sym
    IntegerToRealFn  -> uncurryAssignment $ integerToReal sym
    RealToIntegerFn  -> uncurryAssignment $ realToInteger sym
    PredToIntegerFn  -> uncurryAssignment $ \p ->
      iteM intIte sym p (intLit sym 1) (intLit sym 0)
    IntSeqFn b inc   -> uncurryAssignment $ \idx _ -> do
      intAdd sym b =<< intMul sym inc idx
    RealSeqFn b inc -> uncurryAssignment $ \_ idx -> do
      realAdd sym b =<< realMul sym inc =<< integerToReal sym idx
    IndicesInRange tps0 bnds0 -> \args ->
        Ctx.forIndex (Ctx.size tps0) (g tps0 bnds0 args) (pure (truePred sym))
      where g :: Assignment OnlyIntRepr ctx
              -> Assignment (SymExpr sym) ctx
              -> Assignment (SymExpr sym) ctx
              -> IO (Pred sym)
              -> Index ctx tp
              -> IO (Pred sym)
            g tps bnds args m i = do
              case tps Ctx.! i of
                OnlyIntRepr -> do
                  let v = args ! i
                  let bnd = bnds ! i
                  one <- intLit sym 1
                  p <- join $ andPred sym <$> intLe sym one v <*> intLe sym v bnd
                  andPred sym p =<< m
    IsEqFn{} -> Ctx.uncurryAssignment $ \x y -> do
      isEq sym x y

    BVIsNonZeroFn _    -> Ctx.uncurryAssignment $ bvIsNonzero sym
    ClampedIntNegFn _  -> Ctx.uncurryAssignment $ clampedIntNeg sym
    ClampedIntAbsFn _  -> Ctx.uncurryAssignment $ clampedIntAbs sym
    ClampedIntAddFn _  -> Ctx.uncurryAssignment $ clampedIntAdd sym
    ClampedIntSubFn _  -> Ctx.uncurryAssignment $ clampedIntSub sym
    ClampedIntMulFn _  -> Ctx.uncurryAssignment $ clampedIntMul sym
    ClampedUIntAddFn _ -> Ctx.uncurryAssignment $ clampedUIntAdd sym
    ClampedUIntSubFn _ -> Ctx.uncurryAssignment $ clampedUIntSub sym
    ClampedUIntMulFn _ -> Ctx.uncurryAssignment $ clampedUIntMul sym

    IntSetWidthFn  _ o -> Ctx.uncurryAssignment $ \v -> intSetWidth  sym v o
    UIntSetWidthFn _ o -> Ctx.uncurryAssignment $ \v -> uintSetWidth sym v o
    UIntToIntFn _ o    -> Ctx.uncurryAssignment $ \v -> uintToInt sym v o
    IntToUIntFn _ o    -> Ctx.uncurryAssignment $ \v -> intToUInt sym v o

    RealIsNonZeroFn    -> Ctx.uncurryAssignment $ realIsNonZero sym
    RealCosFn          -> Ctx.uncurryAssignment $ realCos sym
    RealSinFn          -> Ctx.uncurryAssignment $ realSin sym

    RealToSBVFn w      -> Ctx.uncurryAssignment $ \v -> realToSBV sym v w
    RealToUBVFn w      -> Ctx.uncurryAssignment $ \v -> realToBV  sym v w
    PredToBVFn  w      -> Ctx.uncurryAssignment $ \v -> predToBV  sym v w

    CplxIsNonZeroFn  -> Ctx.uncurryAssignment $ \x -> do
      (real_x :+ imag_x) <- cplxGetParts sym x
      join $ orPred sym <$> realIsNonZero sym real_x <*> realIsNonZero sym imag_x
    CplxIsRealFn     -> Ctx.uncurryAssignment $ isReal sym
    RealToComplexFn  -> Ctx.uncurryAssignment $ cplxFromReal sym
    RealPartOfCplxFn -> Ctx.uncurryAssignment $ getRealPart sym
    ImagPartOfCplxFn -> Ctx.uncurryAssignment $ getImagPart sym

    CplxNegFn        -> Ctx.uncurryAssignment $ cplxNeg sym
    CplxAddFn        -> Ctx.uncurryAssignment $ cplxAdd sym
    CplxSubFn        -> Ctx.uncurryAssignment $ cplxSub sym
    CplxMulFn        -> Ctx.uncurryAssignment $ cplxMul sym

    CplxRoundFn      -> Ctx.uncurryAssignment $ cplxRound sym
    CplxFloorFn      -> Ctx.uncurryAssignment $ cplxFloor sym
    CplxCeilFn       -> Ctx.uncurryAssignment $ cplxCeil  sym
    CplxMagFn        -> Ctx.uncurryAssignment $ cplxMag   sym
    CplxSqrtFn       -> Ctx.uncurryAssignment $ cplxSqrt  sym
    CplxExpFn        -> Ctx.uncurryAssignment $ cplxExp   sym
    CplxLogFn        -> Ctx.uncurryAssignment $ cplxLog   sym
    CplxLogBaseFn b  -> Ctx.uncurryAssignment $ cplxLogBase (toRational b) sym
    CplxSinFn        -> Ctx.uncurryAssignment $ cplxSin  sym
    CplxCosFn        -> Ctx.uncurryAssignment $ cplxCos  sym
    CplxTanFn        -> Ctx.uncurryAssignment $ cplxTan  sym

-- | This class is provides functions needed to implement the symbolic
-- array intrinsic functions
class IsSymExprBuilder sym => MatlabSymbolicArrayBuilder sym where

  -- | Create a Matlab solver function from its prototype.
  mkMatlabSolverFn :: sym
                   -> MatlabSolverFn (SymExpr sym) args ret
                   -> IO (SymFn sym args ret)

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Who2.TestBuilder
  ( TestBuilder
  , newTestBuilder
  ) where

import Data.Parameterized.Nonce (NonceGenerator, Nonce)
import qualified Data.BitVector.Sized as BVS

import What4.BaseTypes (BaseBoolType)
import What4.Interface (IsExprBuilder(..))
import qualified What4.Interface as WI
import qualified What4.Expr as WE
import qualified What4.SemiRing as SR
import What4.Utils.AbstractDomains (AbstractValue, avTop)

import Who2.Expr (Expr(..), HasBaseType(..), mkExpr)
import Who2.Expr.App (App(..))
import Who2.Expr.SymExpr (SymExpr(..))
import qualified Who2.Builder.Ops.BV as BV
import qualified Who2.Expr.BV as EBV
import qualified Who2.Expr.Logic as EL
import qualified Who2.Expr.PolarizedBloomSeq as PBS
import qualified Who2.Expr.SemiRing.Product as SRP
import qualified Who2.Expr.SemiRing.Sum as SRS

-- | A naive builder that bypasses all simplifications by always using
-- "top" (widest possible) abstract values and allocating every expression.
data TestBuilder t = TestBuilder
  { tbNonceGen :: NonceGenerator IO t
  , tbTrue :: SymExpr t BaseBoolType
  , tbFalse :: SymExpr t BaseBoolType
  }

-- | Create a new TestBuilder with naive allocator
newTestBuilder :: NonceGenerator IO t -> IO (TestBuilder t)
newTestBuilder gen = do
  trueExpr <- mkExpr gen (LogicApp EL.TruePred) (Just True)
  falseExpr <- mkExpr gen (LogicApp EL.FalsePred) (Just False)
  pure $ TestBuilder
    { tbNonceGen = gen
    , tbTrue = SymExpr trueExpr
    , tbFalse = SymExpr falseExpr
    }

-- | Compute "top" (widest possible) abstract value for each type
computeTopAbsVal :: App t (Expr t (App t)) tp -> AbstractValue tp
computeTopAbsVal app = avTop (baseType app)

-- | Naive allocator helper
naiveAlloc :: TestBuilder t -> App t (Expr t (App t)) tp -> IO (Expr t (App t) tp)
naiveAlloc tb app = mkExpr (tbNonceGen tb) app (computeTopAbsVal app)

-- | Naive allocator that ignores the provided abstract value
naiveAllocWithAbsVal :: TestBuilder t -> App t (Expr t (App t)) tp -> AbstractValue tp -> IO (Expr t (App t) tp)
naiveAllocWithAbsVal tb app _absVal = naiveAlloc tb app

-- | Type instances for what4 interface
type instance WI.SymExpr (TestBuilder t) = SymExpr t
type instance WI.BoundVar (TestBuilder t) = WE.ExprBoundVar t
type instance WI.SymFn (TestBuilder t) = WE.ExprSymFn t
type instance WI.SymAnnotation (TestBuilder t) = Nonce t

-- | IsExprBuilder instance that delegates to naive operations
instance IsExprBuilder (TestBuilder t) where

  getConfiguration _ = error "TestBuilder.getConfiguration: not implemented"
  setSolverLogListener _ _ = pure ()
  getSolverLogListener _ = pure Nothing
  logSolverEvent = error "TestBuilder.logSolverEvent: not implemented"
  getCurrentProgramLoc = error "TestBuilder.getCurrentProgramLoc: not implemented"
  setCurrentProgramLoc = error "TestBuilder.setCurrentProgramLoc: not implemented"

  annotateTerm = error "TestBuilder.annotateTerm: not implemented"
  getAnnotation = error "TestBuilder.getAnnotation: not implemented"
  getUnannotatedTerm = error "TestBuilder.getUnannotatedTerm: not implemented"

  truePred = tbTrue
  falsePred = tbFalse

  notPred tb x = do
    let SymExpr ex = x
    result <- naiveAlloc tb (LogicApp (EL.NotPred ex))
    pure (SymExpr result)

  andPred tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    case PBS.fromTwo (EL.BoolExprWrapper ex) (EL.BoolExprWrapper ey) of
      PBS.Inconsistent -> pure (tbFalse tb)  -- x && not x = false
      PBS.SinglePositive (EL.BoolExprWrapper e) -> pure (SymExpr e)
      PBS.SingleNegative (EL.BoolExprWrapper e) -> notPred tb (SymExpr e)
      PBS.Merged pbs -> do
        result <- naiveAlloc tb (LogicApp (EL.AndPred pbs))
        pure (SymExpr result)

  orPred tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    case PBS.fromTwo (EL.BoolExprWrapper ex) (EL.BoolExprWrapper ey) of
      PBS.Inconsistent -> pure (tbTrue tb)  -- x || not x = true
      PBS.SinglePositive (EL.BoolExprWrapper e) -> pure (SymExpr e)
      PBS.SingleNegative (EL.BoolExprWrapper e) -> notPred tb (SymExpr e)
      PBS.Merged pbs -> do
        result <- naiveAlloc tb (LogicApp (EL.OrPred pbs))
        pure (SymExpr result)

  xorPred tb x y = do
    -- XOR is NOT(EQ): true when operands are different
    eqResult <- isEq tb x y
    notPred tb eqResult

  isEq tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    result <- naiveAlloc tb (LogicApp (EL.EqPred ex ey))
    pure (SymExpr result)

  eqPred = isEq

  itePred tb c t e = do
    let SymExpr ec = c
        SymExpr et = t
        SymExpr ee = e
    result <- naiveAlloc tb (LogicApp (EL.Ite ec et ee))
    pure (SymExpr result)

  bvLit tb w bv = do
    result <- naiveAlloc tb (BVApp (EBV.BVLit w bv))
    pure (SymExpr result)

  bvAdd tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
        w = EBV.width ex
        sr = SR.SemiRingBVRepr SR.BVArithRepr w
        -- Create weighted sum: 1*ex + 1*ey + 0
        ws = SRS.add (SRS.var sr ex) (SRS.var sr ey)
    result <- naiveAlloc tb (BVApp (EBV.BVAdd w ws))
    pure (SymExpr result)

  bvSub tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    result <- naiveAlloc tb (BVApp (EBV.BVSub (EBV.width ex) ex ey))
    pure (SymExpr result)

  bvMul tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
        w = EBV.width ex
        sr = SR.SemiRingBVRepr SR.BVBitsRepr w
        -- Create product: ex^1 * ey^1
        wp = SRP.mul (SRP.var sr ex) (SRP.var sr ey)
    result <- naiveAlloc tb (BVApp (EBV.BVMul w wp))
    pure (SymExpr result)

  bvNeg tb x = do
    let SymExpr ex = x
    result <- naiveAlloc tb (BVApp (EBV.BVNeg (EBV.width ex) ex))
    pure (SymExpr result)

  bvAndBits tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    case PBS.fromTwo (EBV.BVExprWrapper ex) (EBV.BVExprWrapper ey) of
      PBS.Inconsistent -> bvLit tb (EBV.width ex) (BVS.zero (EBV.width ex))  -- x & ~x = 0
      PBS.SinglePositive (EBV.BVExprWrapper e) -> pure (SymExpr e)
      PBS.SingleNegative (EBV.BVExprWrapper e) -> bvNotBits tb (SymExpr e)
      PBS.Merged pbs -> do
        result <- naiveAlloc tb (BVApp (EBV.BVAndBits (EBV.width ex) pbs))
        pure (SymExpr result)

  bvOrBits tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    case PBS.fromTwo (EBV.BVExprWrapper ex) (EBV.BVExprWrapper ey) of
      PBS.Inconsistent -> bvLit tb (EBV.width ex) (BVS.maxUnsigned (EBV.width ex))  -- x | ~x = ~0
      PBS.SinglePositive (EBV.BVExprWrapper e) -> pure (SymExpr e)
      PBS.SingleNegative (EBV.BVExprWrapper e) -> bvNotBits tb (SymExpr e)
      PBS.Merged pbs -> do
        result <- naiveAlloc tb (BVApp (EBV.BVOrBits (EBV.width ex) pbs))
        pure (SymExpr result)

  bvXorBits tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    result <- naiveAlloc tb (BVApp (EBV.BVXorBits (EBV.width ex) ex ey))
    pure (SymExpr result)

  bvNotBits tb x = do
    let SymExpr ex = x
    result <- naiveAlloc tb (BVApp (EBV.BVNotBits (EBV.width ex) ex))
    pure (SymExpr result)

  bvUlt tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    result <- naiveAlloc tb (LogicApp (EL.BVUlt (EBV.width ex) ex ey))
    pure (SymExpr result)

  bvSlt tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    result <- naiveAlloc tb (LogicApp (EL.BVSlt (EBV.width ex) ex ey))
    pure (SymExpr result)

  bvShl tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    result <- naiveAlloc tb (BVApp (EBV.BVShl (EBV.width ex) ex ey))
    pure (SymExpr result)

  bvLshr tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    result <- naiveAlloc tb (BVApp (EBV.BVLshr (EBV.width ex) ex ey))
    pure (SymExpr result)

  bvAshr tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    result <- naiveAlloc tb (BVApp (EBV.BVAshr (EBV.width ex) ex ey))
    pure (SymExpr result)

  bvIte tb c t e = do
    let SymExpr ec = c
        SymExpr et = t
        SymExpr ee = e
    result <- naiveAlloc tb (LogicApp (EL.Ite ec et ee))
    pure (SymExpr result)

  bvUle tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    result <- naiveAlloc tb (LogicApp (EL.BVUle (EBV.width ex) ex ey))
    pure (SymExpr result)

  bvSle tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    result <- naiveAlloc tb (LogicApp (EL.BVSle (EBV.width ex) ex ey))
    pure (SymExpr result)

  bvUdiv tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    result <- naiveAlloc tb (BVApp (EBV.BVUdiv (EBV.width ex) ex ey))
    pure (SymExpr result)

  bvUrem tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    result <- naiveAlloc tb (BVApp (EBV.BVUrem (EBV.width ex) ex ey))
    pure (SymExpr result)

  bvSdiv tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    result <- naiveAlloc tb (BVApp (EBV.BVSdiv (EBV.width ex) ex ey))
    pure (SymExpr result)

  bvSrem tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    result <- naiveAlloc tb (BVApp (EBV.BVSrem (EBV.width ex) ex ey))
    pure (SymExpr result)

  bvRol tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    result <- naiveAlloc tb (BVApp (EBV.BVRol (EBV.width ex) ex ey))
    pure (SymExpr result)

  bvRor tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    result <- naiveAlloc tb (BVApp (EBV.BVRor (EBV.width ex) ex ey))
    pure (SymExpr result)

  bvConcat tb x y = do
    let SymExpr ex = x
        SymExpr ey = y
    result <- BV.bvConcat (naiveAllocWithAbsVal tb . BVApp) ex ey
    pure (SymExpr result)

  bvSelect tb idx n x = do
    let SymExpr ex = x
    result <- BV.bvSelect (naiveAllocWithAbsVal tb . BVApp) idx n ex
    pure (SymExpr result)

  bvZext tb w' x = do
    let SymExpr ex = x
    result <- BV.bvZext (naiveAllocWithAbsVal tb . BVApp) w' ex
    pure (SymExpr result)

  bvSext tb w' x = do
    let SymExpr ex = x
    result <- BV.bvSext (naiveAllocWithAbsVal tb . BVApp) w' ex
    pure (SymExpr result)

  -- Stubs for other required methods (not yet implemented)
  bvEq = isEq
  bvFill = error "TestBuilder.bvFill: not implemented"
  testBitBV = error "TestBuilder.testBitBV: not implemented"
  bvIsNonzero = error "TestBuilder.bvIsNonzero: not implemented"
  bvPopcount = error "TestBuilder.bvPopcount: not implemented"
  bvCountTrailingZeros = error "TestBuilder.bvCountTrailingZeros: not implemented"
  bvCountLeadingZeros = error "TestBuilder.bvCountLeadingZeros: not implemented"

  mkStruct = error "TestBuilder.mkStruct: not implemented"
  structField = error "TestBuilder.structField: not implemented"
  structIte = error "TestBuilder.structIte: not implemented"

  constantArray = error "TestBuilder.constantArray: not implemented"
  arrayFromFn = error "TestBuilder.arrayFromFn: not implemented"
  arrayMap = error "TestBuilder.arrayMap: not implemented"
  arrayUpdate = error "TestBuilder.arrayUpdate: not implemented"
  arrayLookup = error "TestBuilder.arrayLookup: not implemented"
  arrayEq = error "TestBuilder.arrayEq: not implemented"
  arrayTrueOnEntries = error "TestBuilder.arrayTrueOnEntries: not implemented"
  arrayIte = error "TestBuilder.arrayIte: not implemented"
  arrayCopy = error "TestBuilder.arrayCopy: not implemented"
  arraySet = error "TestBuilder.arraySet: not implemented"
  arrayRangeEq = error "TestBuilder.arrayRangeEq: not implemented"

  intLit = error "TestBuilder.intLit: not implemented"
  intNeg = error "TestBuilder.intNeg: not implemented"
  intAdd = error "TestBuilder.intAdd: not implemented"
  intSub = error "TestBuilder.intSub: not implemented"
  intMul = error "TestBuilder.intMul: not implemented"
  intDiv = error "TestBuilder.intDiv: not implemented"
  intMod = error "TestBuilder.intMod: not implemented"
  intAbs = error "TestBuilder.intAbs: not implemented"
  intDivisible = error "TestBuilder.intDivisible: not implemented"
  intIte = error "TestBuilder.intIte: not implemented"
  intEq = error "TestBuilder.intEq: not implemented"
  intLe = error "TestBuilder.intLe: not implemented"
  intLt = error "TestBuilder.intLt: not implemented"
  bvToInteger = error "TestBuilder.bvToInteger: not implemented"
  sbvToInteger = error "TestBuilder.sbvToInteger: not implemented"
  integerToBV = error "TestBuilder.integerToBV: not implemented"
  integerToReal = error "TestBuilder.integerToReal: not implemented"
  predToBV = error "TestBuilder.predToBV: not implemented"

  realZero = error "TestBuilder.realZero: not implemented"
  realLit = error "TestBuilder.realLit: not implemented"
  realNeg = error "TestBuilder.realNeg: not implemented"
  realAdd = error "TestBuilder.realAdd: not implemented"
  realSub = error "TestBuilder.realSub: not implemented"
  realMul = error "TestBuilder.realMul: not implemented"
  realDiv = error "TestBuilder.realDiv: not implemented"
  realSqrt = error "TestBuilder.realSqrt: not implemented"
  realIte = error "TestBuilder.realIte: not implemented"
  realEq = error "TestBuilder.realEq: not implemented"
  realLe = error "TestBuilder.realLe: not implemented"
  realLt = error "TestBuilder.realLt: not implemented"
  realToInteger = error "TestBuilder.realToInteger: not implemented"
  realMod = error "TestBuilder.realMod: not implemented"
  sbvToReal = error "TestBuilder.sbvToReal: not implemented"
  realToBV = error "TestBuilder.realToBV: not implemented"
  realToSBV = error "TestBuilder.realToSBV: not implemented"
  realRoundEven = error "TestBuilder.realRoundEven: not implemented"
  realRound = error "TestBuilder.realRound: not implemented"
  realFloor = error "TestBuilder.realFloor: not implemented"
  realCeil = error "TestBuilder.realCeil: not implemented"
  isInteger = error "TestBuilder.isInteger: not implemented"
  realSpecialFunction = error "TestBuilder.realSpecialFunction: not implemented"
  realSin = error "TestBuilder.realSin: not implemented"
  realCos = error "TestBuilder.realCos: not implemented"
  realTan = error "TestBuilder.realTan: not implemented"
  realSinh = error "TestBuilder.realSinh: not implemented"
  realCosh = error "TestBuilder.realCosh: not implemented"
  realTanh = error "TestBuilder.realTanh: not implemented"
  realExp = error "TestBuilder.realExp: not implemented"
  realLog = error "TestBuilder.realLog: not implemented"
  realAtan2 = error "TestBuilder.realAtan2: not implemented"

  floatPZero = error "TestBuilder.floatPZero: not implemented"
  floatNZero = error "TestBuilder.floatNZero: not implemented"
  floatNaN = error "TestBuilder.floatNaN: not implemented"
  floatPInf = error "TestBuilder.floatPInf: not implemented"
  floatNInf = error "TestBuilder.floatNInf: not implemented"
  floatLit = error "TestBuilder.floatLit: not implemented"
  floatNeg = error "TestBuilder.floatNeg: not implemented"
  floatAbs = error "TestBuilder.floatAbs: not implemented"
  floatSqrt = error "TestBuilder.floatSqrt: not implemented"
  floatAdd = error "TestBuilder.floatAdd: not implemented"
  floatSub = error "TestBuilder.floatSub: not implemented"
  floatMul = error "TestBuilder.floatMul: not implemented"
  floatDiv = error "TestBuilder.floatDiv: not implemented"
  floatRem = error "TestBuilder.floatRem: not implemented"
  floatMin = error "TestBuilder.floatMin: not implemented"
  floatMax = error "TestBuilder.floatMax: not implemented"
  floatFMA = error "TestBuilder.floatFMA: not implemented"
  floatEq = error "TestBuilder.floatEq: not implemented"
  floatNe = error "TestBuilder.floatNe: not implemented"
  floatFpEq = error "TestBuilder.floatFpEq: not implemented"
  floatLe = error "TestBuilder.floatLe: not implemented"
  floatLt = error "TestBuilder.floatLt: not implemented"
  floatGe = error "TestBuilder.floatGe: not implemented"
  floatGt = error "TestBuilder.floatGt: not implemented"
  floatIsNaN = error "TestBuilder.floatIsNaN: not implemented"
  floatIsInf = error "TestBuilder.floatIsInf: not implemented"
  floatIsZero = error "TestBuilder.floatIsZero: not implemented"
  floatIsPos = error "TestBuilder.floatIsPos: not implemented"
  floatIsNeg = error "TestBuilder.floatIsNeg: not implemented"
  floatIsSubnorm = error "TestBuilder.floatIsSubnorm: not implemented"
  floatIsNorm = error "TestBuilder.floatIsNorm: not implemented"
  floatIte = error "TestBuilder.floatIte: not implemented"
  floatCast = error "TestBuilder.floatCast: not implemented"
  floatRound = error "TestBuilder.floatRound: not implemented"
  floatFromBinary = error "TestBuilder.floatFromBinary: not implemented"
  floatToBinary = error "TestBuilder.floatToBinary: not implemented"
  bvToFloat = error "TestBuilder.bvToFloat: not implemented"
  sbvToFloat = error "TestBuilder.sbvToFloat: not implemented"
  realToFloat = error "TestBuilder.realToFloat: not implemented"
  floatToBV = error "TestBuilder.floatToBV: not implemented"
  floatToSBV = error "TestBuilder.floatToSBV: not implemented"
  floatToReal = error "TestBuilder.floatToReal: not implemented"
  floatSpecialFunction = error "TestBuilder.floatSpecialFunction: not implemented"

  mkComplex = error "TestBuilder.mkComplex: not implemented"
  getRealPart = error "TestBuilder.getRealPart: not implemented"
  getImagPart = error "TestBuilder.getImagPart: not implemented"
  cplxGetParts = error "TestBuilder.cplxGetParts: not implemented"

  stringEmpty = error "TestBuilder.stringEmpty: not implemented"
  stringLit = error "TestBuilder.stringLit: not implemented"
  stringEq = error "TestBuilder.stringEq: not implemented"
  stringIte = error "TestBuilder.stringIte: not implemented"
  stringIndexOf = error "TestBuilder.stringIndexOf: not implemented"
  stringContains = error "TestBuilder.stringContains: not implemented"
  stringIsPrefixOf = error "TestBuilder.stringIsPrefixOf: not implemented"
  stringIsSuffixOf = error "TestBuilder.stringIsSuffixOf: not implemented"
  stringSubstring = error "TestBuilder.stringSubstring: not implemented"
  stringConcat = error "TestBuilder.stringConcat: not implemented"
  stringLength = error "TestBuilder.stringLength: not implemented"

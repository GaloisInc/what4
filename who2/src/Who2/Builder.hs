{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | A faster but less featureful alternative to 'What4.Expr.Builder.ExprBuilder'.
module Who2.Builder
  ( Builder
  , newBuilder
  ) where

import Data.Coerce (coerce)
import qualified Data.IntMap.Strict as IntMap

import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Map as MapF
import Data.Parameterized.Nonce (Nonce, NonceGenerator)
import qualified Data.Parameterized.Nonce as Nonce
import Data.Parameterized.TraversableFC (fmapFC)

import qualified What4.Expr as WE
import qualified What4.Expr.App as WEA
import qualified What4.Interface as WI
import What4.Utils.AbstractDomains (AbstractValue, avTop)
import qualified What4.ProgramLoc as WPL
import qualified What4.Utils.BVDomain as BVD

import qualified Who2.Builder.Allocator as BA
import qualified Who2.Builder.Ops.BV as BV
import qualified Who2.Builder.Ops.Logic as Logic
import Who2.Expr (Expr)
import qualified Who2.Expr as E
import qualified Who2.Expr.App as EA
import Who2.Expr.App (App)
import qualified Who2.Expr.Fn as EFn
import qualified Who2.Expr.Logic as EL
import qualified Who2.Expr.SymFn as ESF
import qualified Who2.Expr.Subst as Subst
import Who2.Expr.SymExpr (SymExpr(SymExpr, getSymExpr))

-- | A faster but less featureful alternative to 'What4.Expr.Builder.ExprBuilder'.
--
-- 'Builder' is an instance of 'WI.IsExprBuilder' and 'WI.IsSymExprBuilder'.
--
-- Benchmarking and profiling with @w4smt2-bench@ shows that
-- 'What4.Expr.Builder.ExprBuilder' adds considerable overhead to SMT queries,
-- and that this overhead largely arises from What4's normalizing data
-- structures (see "What4.Expr.App"). Such data structures can make building
-- expressions take @O(n log n)@. 'Builder' performs local rewrites and tracks
-- abstract domains, but does not include such heavyweight datastructures.
-- It strives to keep construction approximately linear.
data Builder t
  = Builder
    { bAllocator :: !(BA.ExprAllocator t)
    , bNonceGen :: !(NonceGenerator IO t)
    , bTrue :: !(SymExpr t WI.BaseBoolType)
    , bFalse :: !(SymExpr t WI.BaseBoolType)
    }

-- | Create a new 'Builder'
newBuilder :: NonceGenerator IO t -> IO (Builder t)
newBuilder g = do
  let allocator = BA.simpleAllocator g
  trueExpr <- toSymExpr $ BA.riskyAllocExpr allocator (EA.LogicApp EL.TruePred) (Just True)
  falseExpr <- toSymExpr $ BA.riskyAllocExpr allocator (EA.LogicApp EL.FalsePred) (Just False)
  return Builder
    { bAllocator = allocator
    , bNonceGen = g
    , bTrue = trueExpr
    , bFalse = falseExpr
    }

-- Internal helper
alloc ::
  Builder t ->
  App t (Expr t (App t)) tp ->
  AbstractValue tp ->
  IO (Expr t (App t) tp)
alloc b = BA.riskyAllocExpr (bAllocator b)
{-# INLINE alloc #-}

toSymExpr :: IO (Expr t (App t) tp) -> IO (SymExpr t tp)
toSymExpr = coerce
{-# INLINE toSymExpr #-}

type instance WI.SymExpr (Builder t) = SymExpr t
type instance WI.BoundVar (Builder t) = WE.ExprBoundVar t
type instance WI.SymFn (Builder t) = ESF.SymFn t (Expr t (App t))
type instance WI.SymAnnotation (Builder t) = Nonce t

instance WI.IsExprBuilder (Builder t) where
  getConfiguration = error "FIXME: getConfiguration"
  setSolverLogListener = error "FIXME: setSolverLogListener"
  getSolverLogListener = error "FIXME: getSolverLogListener"
  logSolverEvent = error "FIXME: logSolverEvent"
  getCurrentProgramLoc = error "FIXME: getCurrentProgramLoc"
  setCurrentProgramLoc = error "FIXME: setCurrentProgramLoc"

  annotateTerm = error "FIXME: annotateTerm"
  getAnnotation = error "FIXME: getAnnotation"
  getUnannotatedTerm = error "FIXME: getUnannotatedTerm"

  truePred = bTrue
  falsePred = bFalse
  andPred b (SymExpr x) (SymExpr y) =
    toSymExpr $ Logic.andPred (getSymExpr (bTrue b)) (getSymExpr (bFalse b)) (alloc b . EA.LogicApp) x y
  eqPred b (SymExpr x) (SymExpr y) =
    toSymExpr $ Logic.eq (getSymExpr (bTrue b)) (getSymExpr (bFalse b)) (alloc b . EA.LogicApp) x y
  notPred b (SymExpr x) =
    toSymExpr $ Logic.notPred (getSymExpr (bTrue b)) (getSymExpr (bFalse b)) (alloc b . EA.LogicApp) x
  orPred b (SymExpr x) (SymExpr y) =
    toSymExpr $ Logic.orPred (getSymExpr (bTrue b)) (getSymExpr (bFalse b)) (alloc b . EA.LogicApp) x y
  xorPred b (SymExpr x) (SymExpr y) =
    toSymExpr $ Logic.xorPred (getSymExpr (bTrue b)) (getSymExpr (bFalse b)) (alloc b . EA.LogicApp) x y
  itePred b (SymExpr c) (SymExpr t) (SymExpr f) =
    toSymExpr $ Logic.itePred (getSymExpr (bTrue b)) (getSymExpr (bFalse b)) (alloc b . EA.LogicApp) c t f

  bvLit b w bv =
    toSymExpr (BV.bvLit (alloc b . EA.BVApp) w bv)
  bvAdd b (SymExpr x) (SymExpr y) =
    toSymExpr (BV.bvAdd (alloc b . EA.BVApp) x y)
  bvEq b (SymExpr x) (SymExpr y) =
    toSymExpr $ Logic.eq (getSymExpr (bTrue b)) (getSymExpr (bFalse b))  (alloc b . EA.LogicApp) x y

  bvConcat b (SymExpr x) (SymExpr y) =
    toSymExpr (BV.bvConcat (alloc b . EA.BVApp) x y)
  bvSelect b idx n (SymExpr x) =
    toSymExpr (BV.bvSelect (alloc b . EA.BVApp) idx n x)
  bvNeg b (SymExpr x) =
    toSymExpr (BV.bvNeg (alloc b . EA.BVApp) x)
  bvSub b (SymExpr x) (SymExpr y) =
    toSymExpr (BV.bvSub (alloc b . EA.BVApp) x y)
  bvMul b (SymExpr x) (SymExpr y) =
    toSymExpr (BV.bvMul (alloc b . EA.BVApp) x y)
  bvUdiv b (SymExpr x) (SymExpr y) =
    toSymExpr (BV.bvUdiv (alloc b . EA.BVApp) x y)
  bvUrem b (SymExpr x) (SymExpr y) =
    toSymExpr (BV.bvUrem (alloc b . EA.BVApp) x y)
  bvSdiv b (SymExpr x) (SymExpr y) =
    toSymExpr (BV.bvSdiv (alloc b . EA.BVApp) x y)
  bvSrem b (SymExpr x) (SymExpr y) =
    toSymExpr (BV.bvSrem (alloc b . EA.BVApp) x y)
  testBitBV = error "FIXME: testBitBV"
  bvIte b (SymExpr c) (SymExpr t) (SymExpr f) =
    toSymExpr (Logic.ite (alloc b . EA.LogicApp) c t f)
  bvUlt b (SymExpr x) (SymExpr y) =
    toSymExpr (Logic.bvUlt (getSymExpr (bTrue b)) (getSymExpr (bFalse b)) (alloc b . EA.LogicApp) x y)
  bvSlt b (SymExpr x) (SymExpr y) =
    toSymExpr (Logic.bvSlt (getSymExpr (bTrue b)) (getSymExpr (bFalse b)) (alloc b . EA.LogicApp) x y)
  bvIsNonzero b (SymExpr x) =
    toSymExpr (Logic.bvIsNonzero (getSymExpr (bTrue b)) (getSymExpr (bFalse b)) (alloc b . EA.LogicApp) (coerce . BV.bvLit (alloc b . EA.BVApp)) x)
  bvShl b (SymExpr x) (SymExpr y) =
    toSymExpr (BV.bvShl (alloc b . EA.BVApp) x y)
  bvLshr b (SymExpr x) (SymExpr y) =
    toSymExpr (BV.bvLshr (alloc b . EA.BVApp) x y)
  bvAshr b (SymExpr x) (SymExpr y) =
    toSymExpr (BV.bvAshr (alloc b . EA.BVApp) x y)
  bvRol b (SymExpr x) (SymExpr y) =
    toSymExpr (BV.bvRol (alloc b . EA.BVApp) x y)
  bvRor b (SymExpr x) (SymExpr y) =
    toSymExpr (BV.bvRor (alloc b . EA.BVApp) x y)
  bvZext b w (SymExpr x) =
    toSymExpr (BV.bvZext (alloc b . EA.BVApp) w x)

  bvSext b w (SymExpr x) =
    toSymExpr (BV.bvSext (alloc b . EA.BVApp) w x)
  bvAndBits b (SymExpr x) (SymExpr y) =
    toSymExpr (BV.bvAndBits (alloc b . EA.BVApp) x y)
  bvOrBits b (SymExpr x) (SymExpr y) =
    toSymExpr (BV.bvOrBits (alloc b . EA.BVApp) x y)
  bvXorBits b (SymExpr x) (SymExpr y) =
    toSymExpr (BV.bvXorBits (alloc b . EA.BVApp) x y)
  bvNotBits b (SymExpr x) =
    toSymExpr (BV.bvNotBits (alloc b . EA.BVApp) x)
  bvFill = error "FIXME: bvFill"
  bvPopcount = error "FIXME: bvPopcount"
  bvCountLeadingZeros = error "FIXME: bvCountLeadingZeros"
  bvCountTrailingZeros = error "FIXME: bvCountTrailingZeros"
  predToBV = error "FIXME: predToBV"

  mkStruct = error "FIXME: mkStruct"
  structField = error "FIXME: structField"
  structIte = error "FIXME: structIte"

  constantArray = error "FIXME: constantArray"
  arrayFromFn = error "FIXME: arrayFromFn"
  arrayMap = error "FIXME: arrayMap"
  arrayUpdate = error "FIXME: arrayUpdate"
  arrayLookup = error "FIXME: arrayLookup"
  arrayCopy = error "FIXME: arrayCopy"
  arraySet = error "FIXME: arraySet"
  arrayRangeEq = error "FIXME: arrayRangeEq"
  arrayIte = error "FIXME: arrayIte"
  arrayEq = error "FIXME: arrayEq"
  arrayTrueOnEntries = error "FIXME: arrayTrueOnEntries"

  integerToReal = error "FIXME: integerToReal"
  integerToBV = error "FIXME: integerToBV"
  bvToInteger = error "FIXME: bvToInteger"
  sbvToInteger = error "FIXME: sbvToInteger"
  intLit = error "FIXME: intLit"
  intNeg = error "FIXME: intNeg"
  intAdd = error "FIXME: intAdd"
  intMul = error "FIXME: intMul"
  intIte = error "FIXME: intIte"
  intEq = error "FIXME: intEq"
  intLe = error "FIXME: intLe"
  intAbs = error "FIXME: intAbs"
  intDiv = error "FIXME: intDiv"
  intMod = error "FIXME: intMod"
  intDivisible = error "FIXME: intDivisible"

  stringEmpty = error "FIXME: stringEmpty"
  stringLit = error "FIXME: stringLit"
  stringEq = error "FIXME: stringEq"
  stringIte = error "FIXME: stringIte"
  stringConcat = error "FIXME: stringConcat"
  stringContains = error "FIXME: stringContains"
  stringIsPrefixOf = error "FIXME: stringIsPrefixOf"
  stringIsSuffixOf = error "FIXME: stringIsSuffixOf"
  stringIndexOf = error "FIXME: stringIndexOf"
  stringLength = error "FIXME: stringLength"
  stringSubstring = error "FIXME: stringSubstring"

  realRound = error "FIXME: realRound"
  realRoundEven = error "FIXME: realRoundEven"
  realFloor = error "FIXME: realFloor"
  realCeil = error "FIXME: realCeil"
  realToInteger = error "FIXME: realToInteger"
  realZero = error "FIXME: realZero"
  realLit = error "FIXME: realLit"
  realEq = error "FIXME: realEq"
  realLe = error "FIXME: realLe"
  realIte = error "FIXME: realIte"
  realNeg = error "FIXME: realNeg"
  realAdd = error "FIXME: realAdd"
  realMul = error "FIXME: realMul"
  realDiv = error "FIXME: realDiv"
  isInteger = error "FIXME: isInteger"
  realSqrt = error "FIXME: realSqrt"
  realSpecialFunction = error "FIXME: realSpecialFunction"
  floatPZero = error "FIXME: floatPZero"
  floatNZero = error "FIXME: floatNZero"
  floatNaN = error "FIXME: floatNaN"
  floatPInf = error "FIXME: floatPInf"
  floatNInf = error "FIXME: floatNInf"
  floatLit = error "FIXME: floatLit"
  floatNeg = error "FIXME: floatNeg"
  floatAbs = error "FIXME: floatAbs"
  floatSqrt = error "FIXME: floatSqrt"
  floatAdd = error "FIXME: floatAdd"
  floatSub = error "FIXME: floatSub"
  floatMul = error "FIXME: floatMul"
  floatDiv = error "FIXME: floatDiv"
  floatRem = error "FIXME: floatRem"
  floatMin = error "FIXME: floatMin"
  floatMax = error "FIXME: floatMax"
  floatFMA = error "FIXME: floatFMA"
  floatEq = error "FIXME: floatEq"
  floatNe = error "FIXME: floatNe"
  floatFpEq = error "FIXME: floatFpEq"
  floatLe = error "FIXME: floatLe"
  floatLt = error "FIXME: floatLt"
  floatGe = error "FIXME: floatGe"
  floatGt = error "FIXME: floatGt"
  floatIsNaN = error "FIXME: floatIsNaN"
  floatIsInf = error "FIXME: floatIsInf"
  floatIsZero = error "FIXME: floatIsZero"
  floatIsPos = error "FIXME: floatIsPos"
  floatIsNeg = error "FIXME: floatIsNeg"
  floatIsSubnorm = error "FIXME: floatIsSubnorm"
  floatIsNorm = error "FIXME: floatIsNorm"
  floatIte = error "FIXME: floatIte"
  floatCast = error "FIXME: floatCast"
  floatRound = error "FIXME: floatRound"
  floatFromBinary = error "FIXME: floatFromBinary"
  floatToBinary = error "FIXME: floatToBinary"
  bvToFloat = error "FIXME: bvToFloat"
  sbvToFloat = error "FIXME: sbvToFloat"
  realToFloat = error "FIXME: realToFloat"
  floatToBV = error "FIXME: floatToBV"
  floatToSBV = error "FIXME: floatToSBV"
  floatToReal = error "FIXME: floatToReal"
  floatSpecialFunction = error "FIXME: floatSpecialFunction"
  mkComplex = error "FIXME: mkComplex"
  getRealPart = error "FIXME: getRealPart"
  getImagPart = error "FIXME: getImagPart"
  cplxGetParts = error "FIXME: cplxGetParts"

instance WI.IsSymExprBuilder (Builder t) where
  freshConstant b nm tp = do
    n <- Nonce.freshNonce (bNonceGen b)
    let bvar = WEA.BVar
          { WEA.bvarId = n
          , WEA.bvarLoc = WPL.initializationLoc
          , WEA.bvarName = nm
          , WEA.bvarType = tp
          , WEA.bvarKind = WEA.UninterpVarKind
          , WEA.bvarAbstractValue = Nothing
          }
    -- Create an expression wrapping the bound variable
    absVal <- case tp of
      WI.BaseBVRepr w -> return $ BVD.any w
      WI.BaseBoolRepr -> return Nothing
      _ -> error "FIXME: freshConstant: unsupported type"
    toSymExpr $ alloc b (EA.BoundVarApp bvar) absVal
  freshLatch = error "FIXME: freshLatch"

  freshBoundedBV = error "FIXME: freshBoundedBV"
  freshBoundedSBV = error "FIXME: freshBoundedSBV"
  freshBoundedInt = error "FIXME: freshBoundedInt"
  freshBoundedReal = error "FIXME: freshBoundedReal"
  exprUninterpConstants = error "FIXME: exprUninterpConstants"
  freshBoundVar b _emptySymbol tp = do
    n <- Nonce.freshNonce (bNonceGen b)
    return $ WEA.BVar
      { WEA.bvarId = n
      , WEA.bvarLoc = WPL.initializationLoc
      , WEA.bvarName = _emptySymbol
      , WEA.bvarType = tp
      , WEA.bvarKind = WEA.QuantifierVarKind  -- For function parameters
      , WEA.bvarAbstractValue = Nothing
      }
  varExpr _b var =
    -- Get abstract value from the bound var, or use unconstrained if not provided
    let absVal = case WEA.bvarAbstractValue var of
          Just av -> av
          Nothing -> avTop (WEA.bvarType var)
        -- Create expression directly using the bound variable's nonce
        -- to avoid needing IO for fresh nonce allocation
        app = EA.BoundVarApp var
        expr = E.RiskyExpr
          { E.eId = WEA.bvarId var
          , E.eHash = PC.hashWithSaltF 0 app
          , E.eApp = app
          , E.eAbsVal = absVal
          }
    in SymExpr expr
  forallPred = error "FIXME: forallPred"
  existsPred = error "FIXME: existsPred"
  definedFn b nm vars body policy = do
    n <- Nonce.freshNonce (bNonceGen b)
    let bodyExpr = getSymExpr body
        retType = E.baseType bodyExpr
        -- Convert What4's UnfoldPolicy to Who2's UnfoldPolicy
        w5Policy = case policy of
          WI.AlwaysUnfold -> ESF.AlwaysUnfold
          WI.NeverUnfold -> error "Who2 does not support NeverUnfold policy"
          WI.UnfoldConcrete -> error "Who2 does not support UnfoldConcrete policy"
        fn = ESF.SymFn
          { ESF.symFnId = n
          , ESF.symFnName = nm
          , ESF.symFnInfo = ESF.DefinedFnInfo vars bodyExpr w5Policy retType
          , ESF.symFnLoc = WPL.initializationLoc
          }
    return fn
  freshTotalUninterpFn b nm argTypes retType = do
    -- Generate a fresh nonce for this function
    n <- Nonce.freshNonce (bNonceGen b)
    -- Create the SymFn with UninterpFnInfo
    let fn = ESF.SymFn
          { ESF.symFnId = n
          , ESF.symFnName = nm
          , ESF.symFnInfo = ESF.UninterpFnInfo argTypes retType
          , ESF.symFnLoc = WPL.initializationLoc
          }
    return fn
  applySymFn b fn args = do
    -- Unwrap SymExpr arguments to get the underlying Expr values
    let unwrappedArgs = fmapFC getSymExpr args
    -- Call the pure expression-level function
    -- Pass both alloc (for uninterpreted functions) and builder (for defined functions)
    toSymExpr $ EFn.applyFn (alloc b) b fn unwrappedArgs
  substituteBoundVars b subst expr = do
    -- Convert MapF to IntMap for the Subst module
    let substMap = convertMapFToIntMap subst
    -- Use the Subst module to perform substitution
    -- Pass builder to use IsExprBuilder methods
    toSymExpr $ Subst.substituteBoundVars b (getSymExpr expr) substMap
  substituteSymFns = error "FIXME: substituteSymFns"
  transformPredBV2LIA = error "FIXME: transformPredBV2LIA"
  transformSymFnLIA2BV = error "FIXME: transformSymFnLIA2BV"

-- | Convert MapF to IntMap for substitution
convertMapFToIntMap :: MapF.MapF (WE.ExprBoundVar t) (SymExpr t) -> IntMap.IntMap (Subst.SomeExpr t)
convertMapFToIntMap mapf =
  IntMap.fromList
    [ (fromIntegral $ Nonce.indexValue $ WEA.bvarId var, Subst.SomeExpr (getSymExpr val))
    | MapF.Pair var val <- MapF.toList mapf
    ]

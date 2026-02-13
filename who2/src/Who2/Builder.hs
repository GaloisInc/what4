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

import Control.Monad (when)
import Control.Monad.ST (stToIO)
import Data.Coerce (coerce)
import qualified Data.IntMap.Strict as IntMap

import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.HashTable as PH
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
import Who2.Unsupported (unsupported)

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
    { bNonceGen :: !(NonceGenerator IO t)
    , bTrue :: !(SymExpr t WI.BaseBoolType)
    , bFalse :: !(SymExpr t WI.BaseBoolType)
    , bTermCache :: !(PH.HashTable PH.RealWorld (App t (Expr t (App t))) (Expr t (App t)))
    }

-- | Initial cache size (number of buckets)
-- Similar to What4's cacheStartSizeOption (default 100,000)
-- Start smaller for Who2's lightweight design
cacheInitialSize :: Int
cacheInitialSize = 10000
{-# INLINE cacheInitialSize #-}

-- | Create a new 'Builder'
newBuilder :: NonceGenerator IO t -> IO (Builder t)
newBuilder g = do
  -- Create sized hash table for better performance
  cache <- stToIO $ PH.newSized cacheInitialSize

  trueExpr <- toSymExpr $ E.mkExpr g (EA.LogicApp EL.TruePred) (Just True)
  falseExpr <- toSymExpr $ E.mkExpr g (EA.LogicApp EL.FalsePred) (Just False)

  let builder = Builder
        { bNonceGen = g
        , bTrue = trueExpr
        , bFalse = falseExpr
        , bTermCache = cache
        }

  when E.useHashConsing $ do
    let trueApp = EA.LogicApp EL.TruePred
        falseApp = EA.LogicApp EL.FalsePred
    seq trueExpr $ stToIO $ PH.insert cache trueApp (getSymExpr trueExpr)
    seq falseExpr $ stToIO $ PH.insert cache falseApp (getSymExpr falseExpr)

  return builder

-- Internal helper
alloc ::
  Builder t ->
  App t (Expr t (App t)) tp ->
  AbstractValue tp ->
  IO (Expr t (App t) tp)
alloc b app absVal =
  if E.useHashConsing
  then allocWithHashCons b app absVal
  else E.mkExpr (bNonceGen b) app absVal
{-# INLINE alloc #-}

allocWithHashCons ::
  Builder t ->
  App t (Expr t (App t)) tp ->
  AbstractValue tp ->
  IO (Expr t (App t) tp)
allocWithHashCons b app absVal = do
  me <- stToIO $ PH.lookup (bTermCache b) app
  case me of
    Just e -> return e
    Nothing -> do
      newTerm <- E.mkExpr (bNonceGen b) app absVal
      -- Force evaluation before insertion to prevent thunk accumulation
      seq newTerm $ stToIO $ PH.insert (bTermCache b) app newTerm
      return newTerm

toSymExpr :: IO (Expr t (App t) tp) -> IO (SymExpr t tp)
toSymExpr = coerce
{-# INLINE toSymExpr #-}

type instance WI.SymExpr (Builder t) = SymExpr t
type instance WI.BoundVar (Builder t) = WE.ExprBoundVar t
type instance WI.SymFn (Builder t) = ESF.SymFn t (Expr t (App t))
type instance WI.SymAnnotation (Builder t) = Nonce t

instance WI.IsExprBuilder (Builder t) where
  getConfiguration = unsupported "Who2.Builder.getConfiguration"
  setSolverLogListener = unsupported "Who2.Builder.setSolverLogListener"
  getSolverLogListener = unsupported "Who2.Builder.getSolverLogListener"
  logSolverEvent = unsupported "Who2.Builder.logSolverEvent"
  getCurrentProgramLoc = unsupported "Who2.Builder.getCurrentProgramLoc"
  setCurrentProgramLoc = unsupported "Who2.Builder.setCurrentProgramLoc"

  annotateTerm = unsupported "Who2.Builder.annotateTerm"
  getAnnotation = unsupported "Who2.Builder.getAnnotation"
  getUnannotatedTerm = unsupported "Who2.Builder.getUnannotatedTerm"

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
  testBitBV = unsupported "Who2.Builder.testBitBV"
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
  bvFill = unsupported "Who2.Builder.bvFill"
  bvPopcount = unsupported "Who2.Builder.bvPopcount"
  bvCountLeadingZeros = unsupported "Who2.Builder.bvCountLeadingZeros"
  bvCountTrailingZeros = unsupported "Who2.Builder.bvCountTrailingZeros"
  predToBV = unsupported "Who2.Builder.predToBV"

  mkStruct = unsupported "Who2.Builder.mkStruct"
  structField = unsupported "Who2.Builder.structField"
  structIte = unsupported "Who2.Builder.structIte"

  constantArray = unsupported "Who2.Builder.constantArray"
  arrayFromFn = unsupported "Who2.Builder.arrayFromFn"
  arrayMap = unsupported "Who2.Builder.arrayMap"
  arrayUpdate = unsupported "Who2.Builder.arrayUpdate"
  arrayLookup = unsupported "Who2.Builder.arrayLookup"
  arrayCopy = unsupported "Who2.Builder.arrayCopy"
  arraySet = unsupported "Who2.Builder.arraySet"
  arrayRangeEq = unsupported "Who2.Builder.arrayRangeEq"
  arrayIte = unsupported "Who2.Builder.arrayIte"
  arrayEq = unsupported "Who2.Builder.arrayEq"
  arrayTrueOnEntries = unsupported "Who2.Builder.arrayTrueOnEntries"

  integerToReal = unsupported "Who2.Builder.integerToReal"
  integerToBV = unsupported "Who2.Builder.integerToBV"
  bvToInteger = unsupported "Who2.Builder.bvToInteger"
  sbvToInteger = unsupported "Who2.Builder.sbvToInteger"
  intLit = unsupported "Who2.Builder.intLit"
  intNeg = unsupported "Who2.Builder.intNeg"
  intAdd = unsupported "Who2.Builder.intAdd"
  intMul = unsupported "Who2.Builder.intMul"
  intIte = unsupported "Who2.Builder.intIte"
  intEq = unsupported "Who2.Builder.intEq"
  intLe = unsupported "Who2.Builder.intLe"
  intAbs = unsupported "Who2.Builder.intAbs"
  intDiv = unsupported "Who2.Builder.intDiv"
  intMod = unsupported "Who2.Builder.intMod"
  intDivisible = unsupported "Who2.Builder.intDivisible"

  stringEmpty = unsupported "Who2.Builder.stringEmpty"
  stringLit = unsupported "Who2.Builder.stringLit"
  stringEq = unsupported "Who2.Builder.stringEq"
  stringIte = unsupported "Who2.Builder.stringIte"
  stringConcat = unsupported "Who2.Builder.stringConcat"
  stringContains = unsupported "Who2.Builder.stringContains"
  stringIsPrefixOf = unsupported "Who2.Builder.stringIsPrefixOf"
  stringIsSuffixOf = unsupported "Who2.Builder.stringIsSuffixOf"
  stringIndexOf = unsupported "Who2.Builder.stringIndexOf"
  stringLength = unsupported "Who2.Builder.stringLength"
  stringSubstring = unsupported "Who2.Builder.stringSubstring"

  realRound = unsupported "Who2.Builder.realRound"
  realRoundEven = unsupported "Who2.Builder.realRoundEven"
  realFloor = unsupported "Who2.Builder.realFloor"
  realCeil = unsupported "Who2.Builder.realCeil"
  realToInteger = unsupported "Who2.Builder.realToInteger"
  realZero = unsupported "Who2.Builder.realZero"
  realLit = unsupported "Who2.Builder.realLit"
  realEq = unsupported "Who2.Builder.realEq"
  realLe = unsupported "Who2.Builder.realLe"
  realIte = unsupported "Who2.Builder.realIte"
  realNeg = unsupported "Who2.Builder.realNeg"
  realAdd = unsupported "Who2.Builder.realAdd"
  realMul = unsupported "Who2.Builder.realMul"
  realDiv = unsupported "Who2.Builder.realDiv"
  isInteger = unsupported "Who2.Builder.isInteger"
  realSqrt = unsupported "Who2.Builder.realSqrt"
  realSpecialFunction = unsupported "Who2.Builder.realSpecialFunction"
  floatPZero = unsupported "Who2.Builder.floatPZero"
  floatNZero = unsupported "Who2.Builder.floatNZero"
  floatNaN = unsupported "Who2.Builder.floatNaN"
  floatPInf = unsupported "Who2.Builder.floatPInf"
  floatNInf = unsupported "Who2.Builder.floatNInf"
  floatLit = unsupported "Who2.Builder.floatLit"
  floatNeg = unsupported "Who2.Builder.floatNeg"
  floatAbs = unsupported "Who2.Builder.floatAbs"
  floatSqrt = unsupported "Who2.Builder.floatSqrt"
  floatAdd = unsupported "Who2.Builder.floatAdd"
  floatSub = unsupported "Who2.Builder.floatSub"
  floatMul = unsupported "Who2.Builder.floatMul"
  floatDiv = unsupported "Who2.Builder.floatDiv"
  floatRem = unsupported "Who2.Builder.floatRem"
  floatMin = unsupported "Who2.Builder.floatMin"
  floatMax = unsupported "Who2.Builder.floatMax"
  floatFMA = unsupported "Who2.Builder.floatFMA"
  floatEq = unsupported "Who2.Builder.floatEq"
  floatNe = unsupported "Who2.Builder.floatNe"
  floatFpEq = unsupported "Who2.Builder.floatFpEq"
  floatLe = unsupported "Who2.Builder.floatLe"
  floatLt = unsupported "Who2.Builder.floatLt"
  floatGe = unsupported "Who2.Builder.floatGe"
  floatGt = unsupported "Who2.Builder.floatGt"
  floatIsNaN = unsupported "Who2.Builder.floatIsNaN"
  floatIsInf = unsupported "Who2.Builder.floatIsInf"
  floatIsZero = unsupported "Who2.Builder.floatIsZero"
  floatIsPos = unsupported "Who2.Builder.floatIsPos"
  floatIsNeg = unsupported "Who2.Builder.floatIsNeg"
  floatIsSubnorm = unsupported "Who2.Builder.floatIsSubnorm"
  floatIsNorm = unsupported "Who2.Builder.floatIsNorm"
  floatIte = unsupported "Who2.Builder.floatIte"
  floatCast = unsupported "Who2.Builder.floatCast"
  floatRound = unsupported "Who2.Builder.floatRound"
  floatFromBinary = unsupported "Who2.Builder.floatFromBinary"
  floatToBinary = unsupported "Who2.Builder.floatToBinary"
  bvToFloat = unsupported "Who2.Builder.bvToFloat"
  sbvToFloat = unsupported "Who2.Builder.sbvToFloat"
  realToFloat = unsupported "Who2.Builder.realToFloat"
  floatToBV = unsupported "Who2.Builder.floatToBV"
  floatToSBV = unsupported "Who2.Builder.floatToSBV"
  floatToReal = unsupported "Who2.Builder.floatToReal"
  floatSpecialFunction = unsupported "Who2.Builder.floatSpecialFunction"
  mkComplex = unsupported "Who2.Builder.mkComplex"
  getRealPart = unsupported "Who2.Builder.getRealPart"
  getImagPart = unsupported "Who2.Builder.getImagPart"
  cplxGetParts = unsupported "Who2.Builder.cplxGetParts"

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
      _ -> unsupported "Who2.Builder.freshConstant: unsupported type"
    toSymExpr $ alloc b (EA.BoundVarApp bvar) absVal
  freshLatch = unsupported "Who2.Builder.freshLatch"

  freshBoundedBV = unsupported "Who2.Builder.freshBoundedBV"
  freshBoundedSBV = unsupported "Who2.Builder.freshBoundedSBV"
  freshBoundedInt = unsupported "Who2.Builder.freshBoundedInt"
  freshBoundedReal = unsupported "Who2.Builder.freshBoundedReal"
  exprUninterpConstants = unsupported "Who2.Builder.exprUninterpConstants"
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
  forallPred = unsupported "Who2.Builder.forallPred"
  existsPred = unsupported "Who2.Builder.existsPred"
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
  substituteSymFns = unsupported "Who2.Builder.substituteSymFns"
  transformPredBV2LIA = unsupported "Who2.Builder.transformPredBV2LIA"
  transformSymFnLIA2BV = unsupported "Who2.Builder.transformSymFnLIA2BV"

-- | Convert MapF to IntMap for substitution
convertMapFToIntMap :: MapF.MapF (WE.ExprBoundVar t) (SymExpr t) -> IntMap.IntMap (Subst.SomeExpr t)
convertMapFToIntMap mapf =
  IntMap.fromList
    [ (fromIntegral $ Nonce.indexValue $ WEA.bvarId var, Subst.SomeExpr (getSymExpr val))
    | MapF.Pair var val <- MapF.toList mapf
    ]

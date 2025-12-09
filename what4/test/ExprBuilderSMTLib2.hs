{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-orphans #-} -- for TestShow instance

import           ProbeSolvers
import           Test.Tasty
import           Test.Tasty.Checklist as TC
import           Test.Tasty.ExpectedFailure
import           Test.Tasty.Hedgehog.Alt
import           Test.Tasty.HUnit

import           Control.Exception (bracket, try, finally, SomeException)
import           Control.Monad (void)
import           Control.Monad.IO.Class (MonadIO(..))
import qualified Data.BitVector.Sized as BV
import           Data.Foldable
import qualified Data.Map as Map
import           Data.Maybe ( fromMaybe )
import           Data.Parameterized.Context ( pattern Empty, pattern (:>) )
import qualified Data.Text as Text
import qualified Hedgehog as H
import qualified Hedgehog.Gen as HGen
import qualified Hedgehog.Range as HRange
import qualified Prettyprinter as PP
import           System.Environment ( lookupEnv )

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           System.IO
import           LibBF

import           What4.BaseTypes
import           What4.Config
import           What4.Expr
import           What4.Interface
import           What4.InterpretedFloatingPoint
import           What4.Protocol.Online
import           What4.Protocol.SMTLib2
import           What4.SatResult
import           What4.Solver.Adapter
import qualified What4.Solver.Bitwuzla as Bitwuzla
import qualified What4.Solver.CVC4 as CVC4
import qualified What4.Solver.CVC5 as CVC5
import qualified What4.Solver.Z3 as Z3
import qualified What4.Solver.Yices as Yices
import qualified What4.Utils.BVDomain as WUB
import qualified What4.Utils.BVDomain.Arith as WUBA
import qualified What4.Utils.ResolveBounds.BV as WURB
import           What4.Utils.StringLiteral
import           What4.Utils.Versions (ver, SolverBounds(..), emptySolverBounds)

data SomePred = forall t . SomePred (BoolExpr t)
deriving instance Show SomePred
type SimpleExprBuilder t fs = ExprBuilder t EmptyExprBuilderState fs

instance TestShow Text.Text where testShow = show
instance TestShow (StringLiteral Unicode) where testShow = show

debugOutputFiles :: Bool
debugOutputFiles = False
--debugOutputFiles = True

maybeClose :: Maybe Handle -> IO ()
maybeClose Nothing = return ()
maybeClose (Just h) = hClose h


userSymbol' :: String -> SolverSymbol
userSymbol' s = case userSymbol s of
  Left e       -> error $ show e
  Right symbol -> symbol

withSym :: FloatModeRepr fm -> (forall t . SimpleExprBuilder t (Flags fm) -> IO a) -> IO a
withSym floatMode pred_gen = withIONonceGenerator $ \gen ->
  pred_gen =<< newExprBuilder floatMode EmptyExprBuilderState gen

withYices :: (forall t. SimpleExprBuilder t (Flags FloatReal) -> SolverProcess t Yices.Connection -> IO a) -> IO a
withYices action = withSym FloatRealRepr $ \sym ->
  do extendConfig Yices.yicesOptions (getConfiguration sym)
     bracket
       (do h <- if debugOutputFiles then Just <$> openFile "yices.out" WriteMode else return Nothing
           s <- startSolverProcess Yices.yicesDefaultFeatures h sym
           return (h,s))
       (\(h,s) -> void $ try @SomeException (shutdownSolverProcess s `finally` maybeClose h))
       (\(_,s) -> action sym s)

withZ3 :: (forall t . SimpleExprBuilder t (Flags FloatIEEE) -> Session t Z3.Z3 -> IO ()) -> IO ()
withZ3 action = withIONonceGenerator $ \nonce_gen -> do
  sym <- newExprBuilder FloatIEEERepr EmptyExprBuilderState nonce_gen
  extendConfig Z3.z3Options (getConfiguration sym)
  Z3.withZ3 sym "z3" defaultLogData { logCallbackVerbose = (\_ -> putStrLn) } (action sym)

withOnlineZ3
  :: (forall t . SimpleExprBuilder t (Flags FloatIEEE) -> SolverProcess t (Writer Z3.Z3) -> IO a)
  -> IO a
withOnlineZ3 action = withSym FloatIEEERepr $ \sym -> do
  extendConfig Z3.z3Options (getConfiguration sym)
  bracket
    (do h <- if debugOutputFiles then Just <$> openFile "z3.out" WriteMode else return Nothing
        s <- startSolverProcess (defaultFeatures Z3.Z3) h sym
        return (h,s))
    (\(h,s) -> void $ try @SomeException (shutdownSolverProcess s `finally` maybeClose h))
    (\(_,s) -> action sym s)

data CVC = CVC4 | CVC5 deriving (Eq, Show)

withCVC4
  :: (forall t . SimpleExprBuilder t (Flags FloatReal) -> SolverProcess t (Writer CVC4.CVC4) -> IO a)
  -> IO a
withCVC4 action = withSym FloatRealRepr $ \sym -> do
  extendConfig CVC4.cvc4Options (getConfiguration sym)
  bracket
    (do h <- if debugOutputFiles then Just <$> openFile "cvc4.out" WriteMode else return Nothing
        s <- startSolverProcess (defaultFeatures CVC4.CVC4) h sym
        return (h,s))
    (\(h,s) -> void $ try @SomeException (shutdownSolverProcess s `finally` maybeClose h))
    (\(_,s) -> action sym s)

withCVC5
  :: (forall t . SimpleExprBuilder t (Flags FloatReal) -> SolverProcess t (Writer CVC5.CVC5) -> IO a)
  -> IO a
withCVC5 action = withSym FloatRealRepr $ \sym -> do
  extendConfig CVC5.cvc5Options (getConfiguration sym)
  bracket
    (do h <- if debugOutputFiles then Just <$> openFile "cvc5.out" WriteMode else return Nothing
        s <- startSolverProcess (defaultFeatures CVC5.CVC5) h sym
        return (h,s))
    (\(h,s) -> void $ try @SomeException (shutdownSolverProcess s `finally` maybeClose h))
    (\(_,s) -> action sym s)

withBitwuzla
  :: (forall t . SimpleExprBuilder t (Flags FloatReal) -> SolverProcess t (Writer Bitwuzla.Bitwuzla) -> IO a)
  -> IO a
withBitwuzla action = withSym FloatRealRepr $ \sym -> do
  extendConfig Bitwuzla.bitwuzlaOptions (getConfiguration sym)
  bracket
    (do h <- if debugOutputFiles then Just <$> openFile "bitwuzla.out" WriteMode else return Nothing
        s <- startSolverProcess (defaultFeatures Bitwuzla.Bitwuzla) h sym
        return (h,s))
    (\(h,s) -> void $ try @SomeException (shutdownSolverProcess s `finally` maybeClose h))
    (\(_,s) -> action sym s)

withModel
  :: Session t Z3.Z3
  -> BoolExpr t
  -> ((forall tp . What4.Expr.Expr t tp -> IO (GroundValue tp)) -> IO ())
  -> IO ()
withModel s p action = do
  assume (sessionWriter s) p
  runCheckSat s $ \case
    Sat (GroundEvalFn {..}, _) -> action groundEval
    Unsat _                    -> "unsat" @?= ("sat" :: String)
    Unknown                    -> "unknown" @?= ("sat" :: String)

-- exists y . (x + 2.0) + (x + 2.0) < y
iFloatTestPred
  :: (  forall t
      . (IsInterpretedFloatExprBuilder (SimpleExprBuilder t fs))
     => SimpleExprBuilder t fs
     -> IO SomePred
     )
iFloatTestPred sym = do
  x  <- freshFloatConstant sym (userSymbol' "x") SingleFloatRepr
  e0 <- iFloatLitSingle sym 2.0
  e1 <- iFloatAdd @_ @SingleFloat sym RNE x e0
  e2 <- iFloatAdd @_ @SingleFloat sym RTZ e1 e1
  y  <- freshFloatBoundVar sym (userSymbol' "y") SingleFloatRepr
  e3 <- iFloatLt @_ @SingleFloat sym e2 $ varExpr sym y
  SomePred <$> existsPred sym y e3

floatSinglePrecision :: FloatPrecisionRepr Prec32
floatSinglePrecision = knownRepr

floatDoublePrecision :: FloatPrecisionRepr Prec64
floatDoublePrecision = knownRepr

floatSingleType :: BaseTypeRepr (BaseFloatType Prec32)
floatSingleType = BaseFloatRepr floatSinglePrecision

floatDoubleType :: BaseTypeRepr (BaseFloatType Prec64)
floatDoubleType = BaseFloatRepr floatDoublePrecision

testInterpretedFloatReal :: TestTree
testInterpretedFloatReal = testCase "Float interpreted as real" $ do
  actual   <- withSym FloatRealRepr iFloatTestPred
  expected <- withSym FloatRealRepr $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") knownRepr
    e0 <- realLit sym 2.0
    e1 <- realAdd sym x e0
    e2 <- realAdd sym e1 e1
    y  <- freshBoundVar sym (userSymbol' "y") knownRepr
    e3 <- realLt sym e2 $ varExpr sym y
    SomePred <$> existsPred sym y e3
  show actual @?= show expected

testFloatUninterpreted :: TestTree
testFloatUninterpreted = testCase "Float uninterpreted" $ do
  actual   <- withSym FloatUninterpretedRepr iFloatTestPred
  expected <- withSym FloatUninterpretedRepr $ \sym -> do
    let bvtp = BaseBVRepr $ knownNat @32
    rne_rm           <- intLit sym $ toInteger $ fromEnum RNE
    rtz_rm           <- intLit sym $ toInteger $ fromEnum RTZ
    x                <- freshConstant sym (userSymbol' "x") knownRepr

    -- Floating point literal: 2.0
    e1 <- bvLit sym knownRepr (BV.mkBV knownRepr (bfToBits (float32 NearEven) (bfFromInt 2)))

    add_fn <- freshTotalUninterpFn
      sym
      (userSymbol' "uninterpreted_float_add")
      (Ctx.empty Ctx.:> BaseIntegerRepr Ctx.:> bvtp Ctx.:> bvtp)
      bvtp
    e2    <- applySymFn sym add_fn $ Ctx.empty Ctx.:> rne_rm Ctx.:> x Ctx.:> e1
    e3    <- applySymFn sym add_fn $ Ctx.empty Ctx.:> rtz_rm Ctx.:> e2 Ctx.:> e2
    y     <- freshBoundVar sym (userSymbol' "y") knownRepr
    lt_fn <- freshTotalUninterpFn sym
                                  (userSymbol' "uninterpreted_float_lt")
                                  (Ctx.empty Ctx.:> bvtp Ctx.:> bvtp)
                                  BaseBoolRepr
    e4 <- applySymFn sym lt_fn $ Ctx.empty Ctx.:> e3 Ctx.:> varExpr sym y
    SomePred <$> existsPred sym y e4
  show actual @?= show expected

testInterpretedFloatIEEE :: TestTree
testInterpretedFloatIEEE = testCase "Float interpreted as IEEE float" $ do
  actual   <- withSym FloatIEEERepr iFloatTestPred
  expected <- withSym FloatIEEERepr $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") knownRepr
    e0 <- floatLitRational sym floatSinglePrecision 2.0
    e1 <- floatAdd sym RNE x e0
    e2 <- floatAdd sym RTZ e1 e1
    y  <- freshBoundVar sym (userSymbol' "y") knownRepr
    e3 <- floatLt sym e2 $ varExpr sym y
    SomePred <$> existsPred sym y e3
  show actual @?= show expected

-- x <= 0.5 && x >= 1.5
testFloatUnsat0 :: TestTree
testFloatUnsat0 = testCase "Unsat float formula" $ withZ3 $ \sym s -> do
  x  <- freshConstant sym (userSymbol' "x") knownRepr
  e0 <- floatLitRational sym floatSinglePrecision 0.5
  e1 <- floatLitRational sym knownRepr 1.5
  p0 <- floatLe sym x e0
  p1 <- floatGe sym x e1
  assume (sessionWriter s) p0
  assume (sessionWriter s) p1
  runCheckSat s $ \res -> isUnsat res @? "unsat"

-- x * x < 0
testFloatUnsat1 :: TestTree
testFloatUnsat1 = testCase "Unsat float formula" $ withZ3 $ \sym s -> do
  x  <- freshConstant sym (userSymbol' "x") floatSingleType
  e0 <- floatMul sym RNE x x
  p0 <- floatIsNeg sym e0
  assume (sessionWriter s) p0
  runCheckSat s $ \res -> isUnsat res @? "unsat"

-- x + y >= x && x != infinity && y > 0 with rounding to +infinity
testFloatUnsat2 :: TestTree
testFloatUnsat2 = testCase "Sat float formula" $ withZ3 $ \sym s -> do
  x  <- freshConstant sym (userSymbol' "x") floatSingleType
  y  <- freshConstant sym (userSymbol' "y") knownRepr
  p0 <- notPred sym =<< floatIsInf sym x
  p1 <- floatIsPos sym y
  p2 <- notPred sym =<< floatIsZero sym y
  e0 <- floatAdd sym RTP x y
  p3 <- floatGe sym x e0
  p4 <- foldlM (andPred sym) (truePred sym) [p1, p2, p3]
  assume (sessionWriter s) p4
  runCheckSat s $ \res -> isSat res @? "sat"
  assume (sessionWriter s) p0
  runCheckSat s $ \res -> isUnsat res @? "unsat"

-- x == 2.5 && y == +infinity
testFloatSat0 :: TestTree
testFloatSat0 = testCase "Sat float formula" $ withZ3 $ \sym s -> do
  x <- freshConstant sym (userSymbol' "x") knownRepr
  e0 <- floatLitRational sym floatSinglePrecision 2.5
  p0 <- floatEq sym x e0
  y <- freshConstant sym (userSymbol' "y") knownRepr
  e1 <- floatPInf sym floatSinglePrecision
  p1 <- floatEq sym y e1
  p2 <- andPred sym p0 p1
  withModel s p2 $ \groundEval -> do
    (@?=) (bfFromDouble 2.5) =<< groundEval x
    y_val <- groundEval y
    assertBool ("expected y = +infinity, actual y = " ++ show y_val) $
      bfIsInf y_val && bfIsPos y_val

-- x >= 0.5 && x <= 1.5
testFloatSat1 :: TestTree
testFloatSat1 = testCase "Sat float formula" $ withZ3 $ \sym s -> do
  x  <- freshConstant sym (userSymbol' "x") knownRepr
  e0 <- floatLitRational sym floatSinglePrecision 0.5
  e1 <- floatLitRational sym knownRepr 1.5
  p0 <- floatGe sym x e0
  p1 <- floatLe sym x e1
  p2 <- andPred sym p0 p1
  withModel s p2 $ \groundEval -> do
    x_val <- groundEval x
    assertBool ("expected x in [0.5, 1.5], actual x = " ++ show x_val) $
      bfFromDouble 0.5 <= x_val && x_val <= bfFromDouble 1.5

testFloatToBinary :: TestTree
testFloatToBinary = testCase "float to binary" $ withZ3 $ \sym s -> do
  x  <- freshConstant sym (userSymbol' "x") knownRepr
  y  <- freshConstant sym (userSymbol' "y") knownRepr
  e0 <- floatToBinary sym x
  e1 <- bvAdd sym e0 y
  e2 <- floatFromBinary sym floatSinglePrecision e1
  p0 <- floatNe sym x e2
  assume (sessionWriter s) p0
  runCheckSat s $ \res -> isSat res @? "sat"
  p1 <- notPred sym =<< bvIsNonzero sym y
  assume (sessionWriter s) p1
  runCheckSat s $ \res -> isUnsat res @? "unsat"

testFloatFromBinary :: TestTree
testFloatFromBinary = testCase "float from binary" $ withZ3 $ \sym s -> do
  x  <- freshConstant sym (userSymbol' "x") knownRepr
  e0 <- floatFromBinary sym floatSinglePrecision x
  e1 <- floatToBinary sym e0
  p0 <- bvNe sym x e1
  assume (sessionWriter s) p0
  runCheckSat s $ \res -> isSat res @? "sat"
  p1 <- notPred sym =<< floatIsNaN sym e0
  assume (sessionWriter s) p1
  runCheckSat s $ \res -> isUnsat res @? "unsat"

testFloatBinarySimplification :: TestTree
testFloatBinarySimplification = testCase "float binary simplification" $
  withSym FloatIEEERepr $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") knownRepr
    e0 <- floatToBinary sym x
    e1 <- floatFromBinary sym floatSinglePrecision e0
    e1 @?= x

testRealFloatBinarySimplification :: TestTree
testRealFloatBinarySimplification =
  testCase "real float binary simplification" $
    withSym FloatRealRepr $ \sym -> do
      x  <- freshFloatConstant sym (userSymbol' "x") SingleFloatRepr
      e0 <- iFloatToBinary sym SingleFloatRepr x
      e1 <- iFloatFromBinary sym SingleFloatRepr e0
      e1 @?= x

testFloatCastSimplification :: TestTree
testFloatCastSimplification = testCase "float cast simplification" $
  withSym FloatIEEERepr $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") floatSingleType
    e0 <- floatCast sym floatDoublePrecision RNE x
    e1 <- floatCast sym floatSinglePrecision RNE e0
    e1 @?= x

testFloatCastNoSimplification :: TestTree
testFloatCastNoSimplification = testCase "float cast no simplification" $
  withSym FloatIEEERepr $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") floatDoubleType
    e0 <- floatCast sym floatSinglePrecision RNE x
    e1 <- floatCast sym floatDoublePrecision RNE e0
    e1 /= x @? ""

testBVSelectShl :: TestTree
testBVSelectShl = testCase "select shl simplification" $
  withSym FloatIEEERepr $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") knownRepr
    e0 <- bvLit sym (knownNat @64) (BV.zero knownNat)
    e1 <- bvConcat sym e0 x
    e2 <- bvShl sym e1 =<< bvLit sym knownRepr (BV.mkBV knownNat 64)
    e3 <- bvSelect sym (knownNat @64) (knownNat @64) e2
    e3 @?= x

testBVSelectLshr :: TestTree
testBVSelectLshr = testCase "select lshr simplification" $
  withSym FloatIEEERepr $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") knownRepr
    e0 <- bvConcat sym x =<< bvLit sym (knownNat @64) (BV.zero knownNat)
    e1 <- bvLshr sym e0 =<< bvLit sym knownRepr (BV.mkBV knownNat 64)
    e2 <- bvSelect sym (knownNat @0) (knownNat @64) e1
    e2 @?= x

testBVOrShlZext :: TestTree
testBVOrShlZext = testCase "bv or-shl-zext -> concat simplification" $
  withSym FloatIEEERepr $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") (BaseBVRepr $ knownNat @8)
    y  <- freshConstant sym (userSymbol' "y") (BaseBVRepr $ knownNat @8)
    e0 <- bvZext sym (knownNat @16) x
    e1 <- bvShl sym e0 =<< bvLit sym knownRepr (BV.mkBV knownNat 8)
    e2 <- bvZext sym (knownNat @16) y
    e3 <- bvOrBits sym e1 e2
    show e3 @?= "bvConcat cx@0:bv cy@1:bv"
    e4 <- bvOrBits sym e2 e1
    show e4 @?= show e3

arrayCopyTest :: TestTree
arrayCopyTest = testCase "arrayCopy" $ withZ3 $ \sym s -> do
  a <- freshConstant sym (userSymbol' "a") (BaseArrayRepr (Ctx.singleton (BaseBVRepr $ knownNat @64)) (BaseBVRepr $ knownNat @8))
  b <- freshConstant sym (userSymbol' "b") knownRepr
  i <- freshConstant sym (userSymbol' "i") (BaseBVRepr $ knownNat @64)
  j <- freshConstant sym (userSymbol' "j") knownRepr
  k <- freshConstant sym (userSymbol' "k") knownRepr
  n <- freshConstant sym (userSymbol' "n") knownRepr

  copy_a_i_b_j_n <- arrayCopy sym a i b j n
  add_i_k <- bvAdd sym i k
  copy_a_i_b_j_n_at_add_i_k <- arrayLookup sym copy_a_i_b_j_n (Ctx.singleton add_i_k)
  add_j_k <- bvAdd sym j k
  b_at_add_j_k <- arrayLookup sym b (Ctx.singleton add_j_k)

  assume (sessionWriter s) =<< bvUle sym i =<< bvLit sym knownRepr (BV.mkBV knownNat 1024)
  assume (sessionWriter s) =<< bvUle sym j =<< bvLit sym knownRepr (BV.mkBV knownNat 1024)
  assume (sessionWriter s) =<< bvUle sym n =<< bvLit sym knownRepr (BV.mkBV knownNat 1024)

  assume (sessionWriter s) =<< bvNe sym copy_a_i_b_j_n_at_add_i_k b_at_add_j_k

  runCheckSat s $ \res -> isSat res @? "sat"

  assume (sessionWriter s) =<< bvUlt sym k n

  runCheckSat s $ \res -> isUnsat res @? "unsat"

arraySetTest :: TestTree
arraySetTest = testCase "arraySet" $ withZ3 $ \sym s -> do
  a <- freshConstant sym (userSymbol' "a") knownRepr
  i <- freshConstant sym (userSymbol' "i") (BaseBVRepr $ knownNat @64)
  j <- freshConstant sym (userSymbol' "j") knownRepr
  n <- freshConstant sym (userSymbol' "n") knownRepr
  v <- freshConstant sym (userSymbol' "v") (BaseBVRepr $ knownNat @8)

  set_a_i_v_n <- arraySet sym a i v n
  add_i_j <- bvAdd sym i j
  set_a_i_v_n_at_add_i_j <- arrayLookup sym set_a_i_v_n (Ctx.singleton add_i_j)

  assume (sessionWriter s) =<< bvUle sym i =<< bvLit sym knownRepr (BV.mkBV knownNat 1024)
  assume (sessionWriter s) =<< bvUle sym n =<< bvLit sym knownRepr (BV.mkBV knownNat 1024)

  assume (sessionWriter s) =<< bvNe sym v set_a_i_v_n_at_add_i_j

  runCheckSat s $ \res -> isSat res @? "sat"

  assume (sessionWriter s) =<< bvUlt sym j n

  runCheckSat s $ \res -> isUnsat res @? "unsat"

arrayCopySetTest :: TestTree
arrayCopySetTest = testCase "arrayCopy/arraySet" $ withZ3 $ \sym s -> do
  a <- freshConstant sym (userSymbol' "a") knownRepr
  i <- freshConstant sym (userSymbol' "i") (BaseBVRepr $ knownNat @64)
  n <- freshConstant sym (userSymbol' "n") knownRepr
  v <- freshConstant sym (userSymbol' "v") (BaseBVRepr $ knownNat @8)

  const_v <- constantArray sym (Ctx.singleton (BaseBVRepr $ knownNat @64)) v
  z <- bvLit sym knownRepr $ BV.mkBV knownNat 0
  copy_a_i_v_n <- arrayCopy sym a i const_v z n
  set_a_i_v_n <- arraySet sym a i v n

  assume (sessionWriter s) =<< bvUle sym i =<< bvLit sym knownRepr (BV.mkBV knownNat 1024)
  assume (sessionWriter s) =<< bvUle sym n =<< bvLit sym knownRepr (BV.mkBV knownNat 1024)

  p <- notPred sym =<< arrayEq sym copy_a_i_v_n set_a_i_v_n

  assume (sessionWriter s) p
  runCheckSat s $ \res -> isUnsat res @? "unsat"

testUninterpretedFunctionScope :: TestTree
testUninterpretedFunctionScope = testCase "uninterpreted function scope" $
  withOnlineZ3 $ \sym s -> do
    fn <- freshTotalUninterpFn sym (userSymbol' "f") knownRepr BaseIntegerRepr
    x  <- freshConstant sym (userSymbol' "x") BaseIntegerRepr
    y  <- freshConstant sym (userSymbol' "y") BaseIntegerRepr
    e0 <- applySymFn sym fn (Ctx.empty Ctx.:> x)
    e1 <- applySymFn sym fn (Ctx.empty Ctx.:> y)
    p0 <- intEq sym x y
    p1 <- notPred sym =<< intEq sym e0 e1
    p2 <- andPred sym p0 p1
    res1 <- checkSatisfiable s "test" p2
    isUnsat res1 @? "unsat"
    res2 <- checkSatisfiable s "test" p2
    isUnsat res2 @? "unsat"

testBVIteNesting :: TestTree
testBVIteNesting = testCase "nested bitvector ites" $ withZ3 $ \sym s -> do
  bv0 <- bvLit sym (knownNat @32) (BV.zero knownNat)
  let setSymBit bv idx = do
        c1 <- freshConstant sym (userSymbol' ("c1_" ++ show idx)) knownRepr
        c2 <- freshConstant sym (userSymbol' ("c2_" ++ show idx)) knownRepr
        c3 <- freshConstant sym (userSymbol' ("c3_" ++ show idx)) knownRepr
        tt1 <- freshConstant sym (userSymbol' ("tt1_" ++ show idx)) knownRepr
        tt2 <- freshConstant sym (userSymbol' ("tt2_" ++ show idx)) knownRepr
        tt3 <- freshConstant sym (userSymbol' ("tt3_" ++ show idx)) knownRepr
        tt4 <- freshConstant sym (userSymbol' ("tt4_" ++ show idx)) knownRepr
        ite1 <- itePred sym c1 tt1 tt2
        ite2 <- itePred sym c2 tt3 tt4
        ite3 <- itePred sym c3 ite1 ite2
        bvSet sym bv idx ite3
  bv1 <- foldlM setSymBit bv0 [0..31]
  p <- testBitBV sym 0 bv1
  assume (sessionWriter s) p
  runCheckSat s $ \res -> isSat res @? "sat"

testRotate1 :: TestTree
testRotate1 = testCase "rotate test1" $ withOnlineZ3 $ \sym s -> do
  bv <- freshConstant sym (userSymbol' "bv") (BaseBVRepr (knownNat @32))

  bv1 <- bvRol sym bv =<< bvLit sym knownNat (BV.mkBV knownNat 8)
  bv2 <- bvRol sym bv1 =<< bvLit sym knownNat (BV.mkBV knownNat 16)
  bv3 <- bvRol sym bv2 =<< bvLit sym knownNat (BV.mkBV knownNat 8)
  bv4 <- bvRor sym bv2 =<< bvLit sym knownNat (BV.mkBV knownNat 24)
  bv5 <- bvRor sym bv2 =<< bvLit sym knownNat (BV.mkBV knownNat 28)

  res <- checkSatisfiable s "test" =<< notPred sym =<< bvEq sym bv bv3
  isUnsat res @? "unsat1"

  res1 <- checkSatisfiable s "test" =<< notPred sym =<< bvEq sym bv bv4
  isUnsat res1 @? "unsat2"

  res2 <- checkSatisfiable s "test" =<< notPred sym =<< bvEq sym bv bv5
  isSat res2 @? "sat"

testRotate2 :: TestTree
testRotate2 = testCase "rotate test2" $ withOnlineZ3 $ \sym s -> do
  bv  <- freshConstant sym (userSymbol' "bv") (BaseBVRepr (knownNat @32))
  amt <- freshConstant sym (userSymbol' "amt") (BaseBVRepr (knownNat @32))

  bv1 <- bvRol sym bv amt
  bv2 <- bvRor sym bv1 amt
  bv3 <- bvRol sym bv =<< bvLit sym knownNat (BV.mkBV knownNat 20)

  bv == bv2 @? "syntactic equality"

  res1 <- checkSatisfiable s "test" =<< notPred sym =<< bvEq sym bv bv2
  isUnsat res1 @? "unsat"

  res2 <- checkSatisfiable s "test" =<< notPred sym =<< bvEq sym bv bv3
  isSat res2 @? "sat"

testRotate3 :: TestTree
testRotate3 = testCase "rotate test3" $ withOnlineZ3 $ \sym s -> do
  bv  <- freshConstant sym (userSymbol' "bv") (BaseBVRepr (knownNat @7))
  amt <- freshConstant sym (userSymbol' "amt") (BaseBVRepr (knownNat @7))

  bv1 <- bvRol sym bv amt
  bv2 <- bvRor sym bv1 amt
  bv3 <- bvRol sym bv =<< bvLit sym knownNat (BV.mkBV knownNat 3)

  -- Note, because 7 is not a power of two, this simplification doesn't quite
  -- work out... it would probably be significant work to make it do so.
  -- bv == bv2 @? "syntactic equality"

  res1 <- checkSatisfiable s "test" =<< notPred sym =<< bvEq sym bv bv2
  isUnsat res1 @? "unsat"

  res2 <- checkSatisfiable s "test" =<< notPred sym =<< bvEq sym bv bv3
  isSat res2 @? "sat"

testSymbolPrimeCharZ3 :: TestTree
testSymbolPrimeCharZ3 = testCase "z3 symbol prime (') char" $
  withZ3 $ \sym s -> do
    x <- freshConstant sym (userSymbol' "x'") knownRepr
    y <- freshConstant sym (userSymbol' "y'") knownRepr
    p <- intLt sym x y
    assume (sessionWriter s) p
    runCheckSat s $ \res -> isSat res @? "sat"

expectFailure :: IO a -> IO ()
expectFailure f = try @SomeException f >>= \case
  Left _ -> return ()
  Right _ -> assertFailure "expectFailure"

testBoundVarAsFree :: TestTree
testBoundVarAsFree = testCase "boundvarasfree" $ withOnlineZ3 $ \sym s -> do
  x <- freshBoundVar sym (userSymbol' "x") BaseBoolRepr
  y <- freshBoundVar sym (userSymbol' "y") BaseBoolRepr
  pz <- freshConstant sym (userSymbol' "pz") BaseBoolRepr

  let px = varExpr sym x
  let py = varExpr sym y

  expectFailure $ checkSatisfiable s "test" px
  expectFailure $ checkSatisfiable s "test" py
  checkSatisfiable s "test" pz >>= \res -> isSat res @? "sat"

  inNewFrameWithVars s [Some x] $ do
    checkSatisfiable s "test" px >>= \res -> isSat res @? "sat"
    expectFailure $ checkSatisfiable s "test" py

  -- Outside the scope of inNewFrameWithVars we can no longer
  -- use the bound variable as free
  expectFailure $ checkSatisfiable s "test" px
  expectFailure $ checkSatisfiable s "test" py


roundingTest ::
  OnlineSolver solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
roundingTest sym solver =
  do r <- freshConstant sym (userSymbol' "r") BaseRealRepr

     let runErrTest nm op errOp =
           do diff <- realAbs sym =<< realSub sym r =<< integerToReal sym =<< op sym r
              p'   <- notPred sym =<< errOp diff
              res  <- checkSatisfiable solver nm p'
              isUnsat res @? nm

     runErrTest "floor"   realFloor (\diff -> realLt sym diff =<< realLit sym 1)
     runErrTest "ceiling" realCeil  (\diff -> realLt sym diff =<< realLit sym 1)
     runErrTest "trunc"   realTrunc (\diff -> realLt sym diff =<< realLit sym 1)
     runErrTest "rna"     realRound (\diff -> realLe sym diff =<< realLit sym 0.5)
     runErrTest "rne"     realRoundEven (\diff -> realLe sym diff =<< realLit sym 0.5)

     -- floor test
     do ri <- integerToReal sym =<< realFloor sym r
        p  <- realLe sym ri r

        res <- checkSatisfiable solver "floorTest" =<< notPred sym p
        isUnsat res @? "floorTest"

     -- ceiling test
     do ri <- integerToReal sym =<< realCeil sym r
        p  <- realLe sym r ri

        res <- checkSatisfiable solver "ceilingTest" =<< notPred sym p
        isUnsat res @? "ceilingTest"

     -- truncate test
     do ri <- integerToReal sym =<< realTrunc sym r
        rabs  <- realAbs sym r
        riabs <- realAbs sym ri
        p  <- realLe sym riabs rabs

        res <- checkSatisfiable solver "truncateTest" =<< notPred sym p
        isUnsat res @? "truncateTest"

     -- round away test
     do ri <- integerToReal sym =<< realRound sym r
        diff <- realAbs sym =<< realSub sym r ri
        ptie <- realEq sym diff =<< realLit sym 0.5
        rabs <- realAbs sym r
        iabs <- realAbs sym ri
        plarge <- realGt sym iabs rabs

        res <- checkSatisfiable solver "rnaTest" =<<
                  andPred sym ptie =<< notPred sym plarge
        isUnsat res @? "rnaTest"

     -- round-to-even test
     do i <- realRoundEven sym r
        ri <- integerToReal sym i
        diff <- realAbs sym =<< realSub sym r ri
        ptie <- realEq sym diff =<< realLit sym 0.5
        ieven <- intDivisible sym i 2

        res <- checkSatisfiable solver "rneTest" =<<
                 andPred sym ptie =<< notPred sym ieven
        isUnsat res @? "rneTest"


zeroTupleTest ::
  OnlineSolver solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
zeroTupleTest sym solver =
    do u <- freshConstant sym (userSymbol' "u") (BaseStructRepr Ctx.Empty)
       s <- mkStruct sym Ctx.Empty

       f <- freshTotalUninterpFn sym (userSymbol' "f")
             (Ctx.Empty Ctx.:> BaseStructRepr Ctx.Empty)
             BaseBoolRepr

       fu <- applySymFn sym f (Ctx.Empty Ctx.:> u)
       fs <- applySymFn sym f (Ctx.Empty Ctx.:> s)

       p <- eqPred sym fu fs

       res1 <- checkSatisfiable solver "test" p
       isSat res1 @? "sat"

       res2 <- checkSatisfiable solver "test" =<< notPred sym p
       isUnsat res2 @? "unsat"

oneTupleTest ::
  OnlineSolver solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
oneTupleTest sym solver =
    do u <- freshConstant sym (userSymbol' "u") (BaseStructRepr (Ctx.Empty Ctx.:> BaseBoolRepr))
       s <- mkStruct sym (Ctx.Empty Ctx.:> backendPred sym False)

       f <- freshTotalUninterpFn sym (userSymbol' "f")
             (Ctx.Empty Ctx.:> BaseStructRepr (Ctx.Empty Ctx.:> BaseBoolRepr))
             BaseBoolRepr

       fu <- applySymFn sym f (Ctx.Empty Ctx.:> u)
       fs <- applySymFn sym f (Ctx.Empty Ctx.:> s)

       p <- eqPred sym fu fs

       res1 <- checkSatisfiable solver "test" p
       isSat res1 @? "sat"

       res2 <- checkSatisfiable solver "test" =<< notPred sym p
       isSat res2 @? "neg sat"


pairTest ::
  OnlineSolver solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
pairTest sym solver =
    do u <- freshConstant sym (userSymbol' "u") (BaseStructRepr (Ctx.Empty Ctx.:> BaseBoolRepr Ctx.:> BaseRealRepr))
       r <- realLit sym 42.0
       s <- mkStruct sym (Ctx.Empty Ctx.:> backendPred sym True Ctx.:> r )

       p <- structEq sym u s

       res1 <- checkSatisfiable solver "test" p
       isSat res1 @? "sat"

       res2 <- checkSatisfiable solver "test" =<< notPred sym p
       isSat res2 @? "neg sat"

stringTest1 ::
  OnlineSolver solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
stringTest1 sym solver = withChecklist "string1" $
  do let bsx = "asdf\nasdf"     -- length 9
     let bsz = "qwe\x1c\&rty"   -- length 7
     let bsw = "QQ\"QQ"         -- length 5

     x <- stringLit sym (UnicodeLiteral bsx)
     y <- freshConstant sym (userSymbol' "str") (BaseStringRepr UnicodeRepr)
     z <- stringLit sym (UnicodeLiteral bsz)
     w <- stringLit sym (UnicodeLiteral bsw)

     s <- stringConcat sym x =<< stringConcat sym y z
     s' <- stringConcat sym s w

     l <- stringLength sym s'

     n <- intLit sym 25
     p <- intEq sym n l

     checkSatisfiableWithModel solver "test" p $ \case
       Sat fn ->
         do UnicodeLiteral slit <- groundEval fn s'
            llit <- groundEval fn n

            slit `checkValues`
              (Empty
               :> Val "model string length" (fromIntegral . Text.length) llit
               :> Got "expected prefix" (Text.isPrefixOf bsx)
               :> Got "expected suffix" (Text.isSuffixOf (bsz <> bsw))
              )

       _ -> fail "expected satisfiable model"

     p2 <- intEq sym l =<< intLit sym 20
     checkSatisfiableWithModel solver "test" p2 $ \case
       Unsat () -> return ()
       _ -> fail "expected unsatifiable model"


stringTest2 ::
  OnlineSolver solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
stringTest2 sym solver = withChecklist "string2" $
  do let bsx = "asdf\nasdf"
     let bsz = "qwe\x1c\&rty"
     let bsw = "QQ\"QQ"

     q <- freshConstant sym (userSymbol' "q") BaseBoolRepr

     x <- stringLit sym (UnicodeLiteral bsx)
     z <- stringLit sym (UnicodeLiteral bsz)
     w <- stringLit sym (UnicodeLiteral bsw)

     a <- freshConstant sym (userSymbol' "stra") (BaseStringRepr UnicodeRepr)
     b <- freshConstant sym (userSymbol' "strb") (BaseStringRepr UnicodeRepr)

     ax <- stringConcat sym x a

     zw <- stringIte sym q z w
     bzw <- stringConcat sym b zw

     l <- stringLength sym zw
     n <- intLit sym 7

     p1 <- stringEq sym ax bzw
     p2 <- intLt sym l n
     p  <- andPred sym p1 p2

     checkSatisfiableWithModel solver "test" p $ \case
       Sat fn ->
         do axlit <- groundEval fn ax
            bzwlit <- groundEval fn bzw
            qlit <- groundEval fn q

            TC.check "correct ite" (False ==) qlit
            TC.check "equal strings" (axlit ==) bzwlit

       _ -> fail "expected satisfable model"

stringTest3 ::
  (OnlineSolver solver)  =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
stringTest3 sym solver = withChecklist "string3" $
  do let bsz = "qwe\x1c\&rtyQQ\"QQ"
     z <- stringLit sym (UnicodeLiteral bsz)

     a <- freshConstant sym (userSymbol' "stra") (BaseStringRepr UnicodeRepr)
     b <- freshConstant sym (userSymbol' "strb") (BaseStringRepr UnicodeRepr)
     c <- freshConstant sym (userSymbol' "strc") (BaseStringRepr UnicodeRepr)

     pfx <- stringIsPrefixOf sym a z
     sfx <- stringIsSuffixOf sym b z

     cnt1 <- stringContains sym z c
     cnt2 <- notPred sym =<< stringContains sym c =<< stringLit sym (UnicodeLiteral "Q")
     cnt3 <- notPred sym =<< stringContains sym c =<< stringLit sym (UnicodeLiteral "q")
     cnt  <- andPred sym cnt1 =<< andPred sym cnt2 cnt3

     lena <- stringLength sym a
     lenb <- stringLength sym b
     lenc <- stringLength sym c

     n <- intLit sym 9

     rnga <- intEq sym lena n
     rngb <- intEq sym lenb n
     rngc <- intEq sym lenc =<< intLit sym 6
     rng  <- andPred sym rnga =<< andPred sym rngb rngc

     p <- andPred sym pfx =<<
          andPred sym sfx =<<
          andPred sym cnt rng

     checkSatisfiableWithModel solver "test" p $ \case
       Sat fn ->
         do alit <- fromUnicodeLit <$> groundEval fn a
            blit <- fromUnicodeLit <$> groundEval fn b
            clit <- fromUnicodeLit <$> groundEval fn c

            bsz `checkValues`
              (Empty
               :> Val "correct prefix" (Text.take 9) alit
               :> Val "correct suffix" (Text.reverse . Text.take 9 . Text.reverse) blit
               :> Val "correct middle" (Text.take 6 . Text.drop 1) clit
              )

       _ -> fail "expected satisfable model"


stringTest4 ::
  OnlineSolver solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
stringTest4 sym solver = withChecklist "string4" $
  do let bsx = "str"
     x <- stringLit sym (UnicodeLiteral bsx)
     a <- freshConstant sym (userSymbol' "stra") (BaseStringRepr UnicodeRepr)
     i <- stringIndexOf sym a x =<< intLit sym 5

     zero <- intLit sym 0
     p <- intLe sym zero i

     checkSatisfiableWithModel solver "test" p $ \case
       Sat fn ->
          do alit <- fromUnicodeLit <$> groundEval fn a
             ilit <- groundEval fn i

             TC.check "correct index" (Text.isPrefixOf bsx) (Text.drop (fromIntegral ilit) alit)
             TC.check "index large enough" (>= 5) ilit

       _ -> fail "expected satisfable model"

     np <- notPred sym p
     lena <- stringLength sym a
     fv <- intLit sym 10
     plen <- intLe sym fv lena
     q <- andPred sym np plen

     checkSatisfiableWithModel solver "test" q $ \case
       Sat fn ->
          do alit <- fromUnicodeLit <$> groundEval fn a
             ilit <- groundEval fn i

             TC.check "substring not found" (not . Text.isInfixOf bsx) (Text.drop 5 alit)
             TC.check "expected neg one index" (== (-1)) ilit

       _ -> fail "expected satisfable model"

stringTest5 ::
  OnlineSolver solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
stringTest5 sym solver = withChecklist "string5" $
  do a <- freshConstant sym (userSymbol' "a") (BaseStringRepr UnicodeRepr)
     off <- freshConstant sym (userSymbol' "off") BaseIntegerRepr
     len <- freshConstant sym (userSymbol' "len") BaseIntegerRepr

     n5 <- intLit sym 5
     n20 <- intLit sym 20

     let qlit = "qwerty"

     sub <- stringSubstring sym a off len
     p1 <- stringEq sym sub =<< stringLit sym (UnicodeLiteral qlit)
     p2 <- intLe sym n5 off
     p3 <- intLe sym n20 =<< stringLength sym a

     p <- andPred sym p1 =<< andPred sym p2 p3

     checkSatisfiableWithModel solver "test" p $ \case
       Sat fn ->
         do alit <- fromUnicodeLit <$> groundEval fn a
            offlit <- groundEval fn off
            lenlit <- groundEval fn len

            let q = Text.take (fromIntegral lenlit) (Text.drop (fromIntegral offlit) alit)

            TC.check "correct substring" (qlit ==) q

       _ -> fail "expected satisfable model"


-- This test verifies that we can correctly round-trip the
-- '\' character. It is a bit of a corner case, since it
-- is is involved in the codepoint escape sequences '\u{abcd}'.
stringTest6 ::
  OnlineSolver solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
stringTest6 sym solver = withChecklist "string6" $
  do let conn = solverConn solver
     x <- freshConstant sym (safeSymbol "x") (BaseStringRepr UnicodeRepr)
     l <- stringLength sym x
     intLit sym 1 >>= isEq sym l >>= assume conn
     stringLit sym (UnicodeLiteral (Text.pack "\\")) >>= isEq sym x >>= assume conn
     checkAndGetModel solver "test" >>= \case
       Sat ge -> do
         v <- groundEval ge x
         TC.check "correct string" (v ==) (UnicodeLiteral (Text.pack "\\"))
       _ -> fail "unsatisfiable"

-- This test asks the solver to produce a sequence of 200 unique characters
-- This helps to ensure that we can correclty recieve and send back to the
-- solver enough characters to exhaust the standard printable ASCII sequence,
-- which ensures that we are testing nontrivial escape sequences.
--
-- We don't verify that any particular string is returned because the solvers
-- make different choices about what characters to return.
stringTest7 ::
  OnlineSolver solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
stringTest7 sym solver = withChecklist "string6" $
  do chars <- getChars sym solver 200
     TC.check "correct number of characters" (length chars ==) 200

getChars ::
  OnlineSolver solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  Integer ->
  IO [Char]
getChars sym solver bound = do
    let conn = solverConn solver
    -- Create string var and constrain its length to 1
    x <- freshConstant sym (safeSymbol "x") (BaseStringRepr UnicodeRepr)
    l <- stringLength sym x
    intLit sym 1 >>= isEq sym l >>= assume conn
    -- Recursively generate characters
    let getModelsRecursive n
          | n >= bound = return ""
          | otherwise =
          checkAndGetModel solver "test" >>= \case
            Sat ge -> do
              v <- groundEval ge x
              -- Exclude value
              stringLit sym v >>= isEq sym x >>= notPred sym >>= assume conn
              let c = Text.head $ fromUnicodeLit v
              cs <- getModelsRecursive (n+1)
              return (c:cs)
            _ -> return []

    cs <- getModelsRecursive 0
    return cs


multidimArrayTest ::
  OnlineSolver solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
multidimArrayTest sym solver =
    do f <- freshConstant sym (userSymbol' "a") $
              BaseArrayRepr (Ctx.empty Ctx.:> BaseBoolRepr Ctx.:> BaseBoolRepr) BaseBoolRepr
       f' <- arrayUpdate sym f (Ctx.empty Ctx.:> falsePred sym Ctx.:> falsePred sym) (falsePred sym)
       p <- arrayLookup sym f' (Ctx.empty Ctx.:> truePred sym Ctx.:> truePred sym)
       checkSatisfiable solver "test" p >>= \case
         Sat _ -> return ()
         _ -> fail "expected satisfiable model"

forallTest ::
  OnlineSolver solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
forallTest sym solver =
    do x <- freshConstant sym (userSymbol' "x") BaseBoolRepr
       y <- freshBoundVar sym (userSymbol' "y") BaseBoolRepr
       p <- forallPred sym y =<< orPred sym x (varExpr sym y)
       np <- notPred sym p

       checkSatisfiableWithModel solver "test" p $ \case
         Sat fn ->
           do b <- groundEval fn x
              (b == True) @? "true result"

         _ -> fail "expected satisfible model"

       checkSatisfiableWithModel solver "test" np $ \case
         Sat fn ->
           do b <- groundEval fn x
              (b == False) @? "false result"

         _ -> fail "expected satisfible model"

binderTupleTest1 ::
  OnlineSolver solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
binderTupleTest1 sym solver =
 do var <- freshBoundVar sym (safeSymbol "v")
               (BaseStructRepr (Ctx.Empty Ctx.:> BaseBoolRepr))
    p0 <- existsPred sym var (truePred sym)
    res <- checkSatisfiable solver "test" p0
    isSat res  @? "sat"

binderTupleTest2 ::
  OnlineSolver solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
binderTupleTest2 sym solver =
  do x <- freshBoundVar sym (userSymbol' "x")
              (BaseStructRepr (Ctx.Empty Ctx.:> BaseIntegerRepr Ctx.:> BaseBoolRepr))
     p <- forallPred sym x =<< structEq sym (varExpr sym x) (varExpr sym x)
     np <- notPred sym p
     checkSatisfiableWithModel solver "test" np $ \case
       Unsat _ -> return ()
       _ -> fail "expected UNSAT"

-- | A regression test for #182.
issue182Test ::
  OnlineSolver solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
issue182Test sym solver = do
    let w = knownNat @64
    arr <- freshConstant sym (safeSymbol "arr")
             (BaseArrayRepr (Ctx.Empty Ctx.:> BaseIntegerRepr)
                            (BaseBVRepr w))
    idxInt <- intLit sym 0
    let idx = Ctx.Empty Ctx.:> idxInt
    let arrLookup = arrayLookup sym arr idx
    elt <- arrLookup
    zeroBV <- bvZero sym w
    p <- bvEq sym elt zeroBV

    checkSatisfiableWithModel solver "test" p $ \case
      Sat fn ->
        do elt' <- arrLookup
           eltEval <- groundEval fn elt'
           (eltEval == BV.zero w) @? "non-zero result"

      _ -> fail "expected satisfible model"

-- | A regression test for #315.
issue315Test ::
  OnlineSolver solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
issue315Test sym solver = do
    let w = knownNat @61
    x <- freshConstant sym (safeSymbol "x") (BaseBVRepr w)
    xsi <- sbvToInteger sym x
    xi <- bvToInteger sym x
    p <- intEq sym xsi xi

    checkSatisfiableWithModel solver "test" p $ \case
      Sat fn ->
        do xEval <- groundEval fn x
           (xEval == BV.zero w) @? "non-zero result"

      _ -> fail "expected satisfible model"

-- | A regression test for #329.
issue329Test ::
  OnlineSolver solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
issue329Test sym solver = do
    -- This test shows that the following proposition (written in Cryptol) is
    -- falsifiable when `x == 2`:
    --
    --   \(x : [2]) -> x == 2 ==> ((toSignedInteger x - 1) == -1)
    let w = knownNat @2
    x <- freshConstant sym (safeSymbol "x") (BaseBVRepr w)
    bvTwo <- bvLit sym w (BV.mkBV w 2)
    xEqBvTwo <- bvEq sym x bvTwo
    notXEqBvTwo <- notPred sym xEqBvTwo
    xsi <- sbvToInteger sym x
    intOne <- intLit sym 1
    intNegOne <- intLit sym (-1)
    xsiDec <- intSub sym xsi intOne
    xsiDecEqIntNegOne <- intEq sym xsiDec intNegOne
    p <- orPred sym notXEqBvTwo xsiDecEqIntNegOne

    -- Check if `p` is not valid for all `x` by checking if its negation
    -- (`notP`) is satisfiable. If `notP` is satisfiable, then we have found a
    -- counterexample to `p`.
    notP <- notPred sym p
    checkSatisfiableWithModel solver "test" notP $ \case
      Sat fn ->
        do xEval <- groundEval fn x
           (xEval == BV.mkBV w 2) @? "result other than 2"

      _ -> fail "expected satisfible model"

-- | These tests simply ensure that no exceptions are raised.
testSolverInfo :: TestTree
testSolverInfo = testGroup "solver info queries" $
  [ testCase "test get solver version" $ withOnlineZ3 $ \_ proc -> do
      let conn = solverConn proc
      getVersion conn
      _ <- versionResult conn
      pure ()
  , testCase "test get solver name" $ withOnlineZ3 $ \_ proc -> do
      let conn = solverConn proc
      getName conn
      nm <- nameResult conn
      nm @?= "Z3"
  ]

testSolverVersion :: TestTree
testSolverVersion = testCase "test solver version bounds" $
  withOnlineZ3 $ \_ proc -> do
    let bnd = emptySolverBounds{ lower = Just $(ver "0") }
    checkSolverVersion' (Map.singleton "Z3" bnd) proc >> return ()

testBVDomainArithScale :: TestTree
testBVDomainArithScale = testCase "bv domain arith scale" $
  withSym FloatIEEERepr $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") (BaseBVRepr $ knownNat @8)
    e0 <- bvZext sym (knownNat @16) x
    e1 <- bvNeg sym e0
    e2 <- bvSub sym e1 =<< bvLit sym knownRepr (BV.mkBV knownNat 1)
    e3 <- bvUgt sym e2 =<< bvLit sym knownRepr (BV.mkBV knownNat 256)
    e3 @?= truePred sym

testBVSwap :: TestTree
testBVSwap = testCase "test bvSwap" $
  withSym FloatIEEERepr $ \sym -> do
    e0 <- bvSwap sym (knownNat @2) =<< bvLit sym knownRepr (BV.mkBV knownNat 1)
    e1 <- bvLit sym knownRepr (BV.mkBV knownNat 256)
    e0 @?= e1

testBVBitreverse :: TestTree
testBVBitreverse = testCase "test bvBitreverse" $
  withSym FloatIEEERepr $ \sym -> do
    e0 <- bvBitreverse sym =<< bvLit sym (knownNat @8) (BV.mkBV knownNat 1)
    e1 <- bvLit sym knownRepr (BV.mkBV knownNat 128)
    e0 @?= e1

-- Test unsafeSetAbstractValue on a simple symbolic expression
testUnsafeSetAbstractValue1 :: TestTree
testUnsafeSetAbstractValue1 = testCase "test unsafeSetAbstractValue1" $
  withSym FloatIEEERepr $ \sym -> do
    let w = knownNat @8

    e1A <- freshConstant sym (userSymbol' "x1") (BaseBVRepr w)
    let e1A' = unsafeSetAbstractValue (WUB.BVDArith (WUBA.range w 2 2)) e1A
    unsignedBVBounds e1A' @?= Just (2, 2)
    e1B <- bvAdd sym e1A' =<< bvOne sym w
    case asBV e1B of
      Just bv -> bv @?= BV.mkBV w 3
      Nothing -> assertFailure $ unlines
        [ "unsafeSetAbstractValue doesn't work as expected for a"
        , "simple symbolic expression"
        ]

-- Test unsafeSetAbstractValue on a compound symbolic expression
testUnsafeSetAbstractValue2 :: TestTree
testUnsafeSetAbstractValue2 = testCase "test unsafeSetAbstractValue2" $
  withSym FloatIEEERepr $ \sym -> do
    let w = knownNat @8
    e2A <- freshConstant sym (userSymbol' "x2A") (BaseBVRepr w)
    e2B <- freshConstant sym (userSymbol' "x2B") (BaseBVRepr w)
    e2C <- bvAdd sym e2A e2B
    (_, e2C') <- annotateTerm sym $ unsafeSetAbstractValue (WUB.BVDArith (WUBA.range w 2 2)) e2C
    unsignedBVBounds e2C' @?= Just (2, 2)
    e2D <- bvAdd sym e2C' =<< bvOne sym w
    case asBV e2D of
      Just bv -> bv @?= BV.mkBV w 3
      Nothing -> assertFailure $ unlines
        [ "unsafeSetAbstractValue doesn't work as expected for a"
        , "compound symbolic expression"
        ]

testResolveSymBV :: WURB.SearchStrategy -> TestTree
testResolveSymBV searchStrat =
  testProperty ("test resolveSymBV (" ++ show (PP.pretty searchStrat) ++ ")") $
  H.property $ do
    let w = knownNat @8
    lb <- H.forAll $ HGen.word8 $ HRange.constant 0 maxBound
    ub <- H.forAll $ HGen.word8 $ HRange.constant lb maxBound

    rbv <- liftIO $ withYices $ \sym proc -> do
      bv <- freshConstant sym (safeSymbol "bv") knownRepr
      p1 <- bvUge sym bv =<< bvLit sym w (BV.mkBV w (toInteger lb))
      p2 <- bvUle sym bv =<< bvLit sym w (BV.mkBV w (toInteger ub))
      p3 <- andPred sym p1 p2
      assume (solverConn proc) p3
      WURB.resolveSymBV sym searchStrat w proc bv

    case rbv of
      WURB.BVConcrete bv -> do
        let bv' = fromInteger $ BV.asUnsigned bv
        lb H.=== bv'
        ub H.=== bv'
      WURB.BVSymbolic bounds -> do
        let (lb', ub') = WUBA.ubounds bounds
        lb H.=== fromInteger lb'
        ub H.=== fromInteger ub'

----------------------------------------------------------------------


main :: IO ()
main = do
  testLevel <- TestLevel . fromMaybe "0" <$> lookupEnv "CI_TEST_LEVEL"
  let solverNames = SolverName <$> [ "bitwuzla", "cvc4", "cvc5", "yices", "z3" ]
  solvers <- reportSolverVersions testLevel id
             =<< (zip solverNames <$> mapM getSolverVersion solverNames)
  let z3Tests =
        let skipPre4_8_11 why =
              let shouldSkip = case lookup (SolverName "z3") solvers of
                    Just (SolverVersion v) -> any (`elem` [ "4.8.8", "4.8.9", "4.8.10" ]) $ words v
                    Nothing -> True
              in if shouldSkip then expectFailBecause why else id
            incompatZ3Strings = "unicode and string escaping not supported for older Z3 versions; upgrade to at least 4.8.11"
        in
        [
          testUninterpretedFunctionScope
        , testRotate1
        , testRotate2
        , testRotate3
        , testBoundVarAsFree
        , testSolverInfo
        , testSolverVersion
        , testFloatUnsat0
        , testFloatUnsat1
        , testFloatUnsat2
        , testFloatSat0
        , testFloatSat1
        , testFloatToBinary
        , testFloatFromBinary
        , testBVIteNesting
        , testSymbolPrimeCharZ3
        , testCase "Z3 0-tuple" $ withOnlineZ3 zeroTupleTest
        , testCase "Z3 1-tuple" $ withOnlineZ3 oneTupleTest
        , testCase "Z3 pair"    $ withOnlineZ3 pairTest
        , testCase "Z3 forall binder" $ withOnlineZ3 forallTest

        , skipPre4_8_11 incompatZ3Strings $ testCase "Z3 string1" $ withOnlineZ3 stringTest1
        , testCase "Z3 string2" $ withOnlineZ3 stringTest2
        , skipPre4_8_11 incompatZ3Strings $ testCase "Z3 string3" $ withOnlineZ3 stringTest3
        , skipPre4_8_11 incompatZ3Strings $ testCase "Z3 string4" $ withOnlineZ3 stringTest4
        , skipPre4_8_11 incompatZ3Strings $ testCase "Z3 string5" $ withOnlineZ3 stringTest5
        , skipPre4_8_11 incompatZ3Strings $ testCase "Z3 string6" $ withOnlineZ3 stringTest6
          -- this test apparently passes on older Z3 despite the escaping changes...
        , testCase "Z3 string7" $ withOnlineZ3 stringTest7

        , testCase "Z3 binder tuple1" $ withOnlineZ3 binderTupleTest1
        , testCase "Z3 binder tuple2" $ withOnlineZ3 binderTupleTest2

        , testCase "Z3 rounding" $ withOnlineZ3 roundingTest

        , testCase "Z3 multidim array"$ withOnlineZ3 multidimArrayTest

        , testCase "Z3 #182 test case" $ withOnlineZ3 issue182Test
        , testCase "Z3 #315 test case" $ withOnlineZ3 issue315Test
        , testCase "Z3 #329 test case" $ withOnlineZ3 issue329Test

        , arrayCopyTest
        , arraySetTest
        , arrayCopySetTest
        ]
  let cvcTests cvc =
        let cvcTestCase name assertion = testCase (show cvc ++ " " ++ name) assertion
            skipPre1_8CVC4 why =
              let shouldSkip = cvc == CVC4 && case lookup (SolverName "cvc4") solvers of
                    Just (SolverVersion v) -> any (`elem` [ "1.7" ]) $ words v
                    Nothing -> True
              in if shouldSkip then expectFailBecause why else id
            unsuppStrings = "unicode and string escaping not supported for older CVC4 versions; upgrade to at least 1.8"
            ignoreCVC4TestBecause reason =
              if cvc == CVC4 then ignoreTestBecause reason else id

            withCVC ::
                 (forall t solver. OnlineSolver solver
                   => SimpleExprBuilder t (Flags FloatReal)
                   -> SolverProcess t solver
                   -> IO a)
              -> IO a
            withCVC k =
              case cvc of
                CVC4 -> withCVC4 k
                CVC5 -> withCVC5 k
        in
        [
          ignoreCVC4TestBecause "This test stalls the solver for some reason; line-buffering issue?" $
          cvcTestCase "0-tuple" $ withCVC zeroTupleTest
        , cvcTestCase "1-tuple" $ withCVC oneTupleTest
        , cvcTestCase "pair"    $ withCVC pairTest
        , cvcTestCase "forall binder" $ withCVC forallTest

        , cvcTestCase "string1" $ withCVC stringTest1
        , cvcTestCase "string2" $ withCVC stringTest2
        , skipPre1_8CVC4 unsuppStrings $ cvcTestCase "string3" $ withCVC stringTest3
        , cvcTestCase "string4" $ withCVC stringTest4
        , cvcTestCase "string5" $ withCVC stringTest5
        , skipPre1_8CVC4 unsuppStrings $ cvcTestCase "string6" $ withCVC stringTest6
        , cvcTestCase "string7" $ withCVC stringTest7

        , cvcTestCase "binder tuple1" $ withCVC binderTupleTest1
        , cvcTestCase "binder tuple2" $ withCVC binderTupleTest2

        , cvcTestCase "rounding" $ withCVC roundingTest

        , cvcTestCase "multidim array"$ withCVC multidimArrayTest

        , cvcTestCase "#182 test case" $ withCVC issue182Test
        , cvcTestCase "#315 test case" $ withCVC issue315Test
        , cvcTestCase "#329 test case" $ withCVC issue329Test
        ]
  let cvc4Tests = cvcTests CVC4
  let cvc5Tests = cvcTests CVC5
  let yicesTests =
        [
          testResolveSymBV WURB.ExponentialSearch
        , testResolveSymBV WURB.BinarySearch

        , testCase "Yices 0-tuple" $ withYices zeroTupleTest
        , testCase "Yices 1-tuple" $ withYices oneTupleTest
        , testCase "Yices pair"    $ withYices pairTest
        , testCase "Yices rounding" $ withYices roundingTest
        , testCase "Yices #182 test case" $ withYices issue182Test
        , testCase "Yices #315 test case" $ withYices issue315Test
        , testCase "Yices #329 test case" $ withYices issue329Test
        ]
  let bitwuzlaTests =
        [ testCase "Bitwuzla multidim array" $ withBitwuzla multidimArrayTest
        ]
  let skipIfNotPresent nm = if SolverName nm `elem` (fst <$> solvers) then id
                            else fmap (ignoreTestBecause (nm <> " not present"))
  defaultMain $ testGroup "Tests" $
    [ testInterpretedFloatReal
    , testFloatUninterpreted
    , testInterpretedFloatIEEE
    , testFloatBinarySimplification
    , testRealFloatBinarySimplification
    , testFloatCastSimplification
    , testFloatCastNoSimplification
    , testBVSelectShl
    , testBVSelectLshr
    , testBVOrShlZext
    , testBVDomainArithScale
    , testBVSwap
    , testBVBitreverse
    , testUnsafeSetAbstractValue1
    , testUnsafeSetAbstractValue2
    ]
    <> (skipIfNotPresent "bitwuzla" bitwuzlaTests)
    <> (skipIfNotPresent "cvc4" cvc4Tests)
    <> (skipIfNotPresent "cvc5" cvc5Tests)
    <> (skipIfNotPresent "yices" yicesTests)
    <> (skipIfNotPresent "z3" z3Tests)

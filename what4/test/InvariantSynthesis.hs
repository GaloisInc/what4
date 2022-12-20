{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

import           Test.Tasty
import           Test.Tasty.HUnit

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Context
import           Data.Parameterized.Nonce

import           What4.Config
import           What4.Expr
import           What4.Interface
import           What4.SatResult
import           What4.Solver.Adapter
import qualified What4.Solver.CVC5 as CVC5
import qualified What4.Solver.Z3 as Z3

type SimpleExprBuilder t fs = ExprBuilder t EmptyExprBuilderState fs

logData :: LogData
logData = defaultLogData { logCallbackVerbose = (\_ -> putStrLn) }

withSym :: FloatModeRepr fm -> (forall t . SimpleExprBuilder t (Flags fm) -> IO a) -> IO a
withSym float_mode action = withIONonceGenerator $ \gen -> do
  sym <- newExprBuilder float_mode EmptyExprBuilderState gen
  extendConfig CVC5.cvc5Options (getConfiguration sym)
  extendConfig Z3.z3Options (getConfiguration sym)
  action sym

intTest :: TestTree
intTest = testCase "int test" $ withSym FloatIEEERepr $ \sym -> do
  inv <- freshTotalUninterpFn sym (safeSymbol "inv") knownRepr knownRepr
  i <- freshConstant sym (safeSymbol "i") knownRepr
  n <- freshConstant sym (safeSymbol "n") knownRepr
  zero <- intLit sym 0
  one <- intLit sym 1
  lt_1_n <- intLt sym one n
  inv_0_n <- applySymFn sym inv $ Empty :> zero :> n
  -- 1 < n ==> inv(0, n)
  impl0 <- impliesPred sym lt_1_n inv_0_n
  inv_i_n <- applySymFn sym inv $ Empty :> i :> n
  add_i_1 <- intAdd sym i one
  lt_add_i_1_n <- intLt sym add_i_1 n
  conj0 <- andPred sym inv_i_n lt_add_i_1_n
  inv_add_i_1_n <- applySymFn sym inv $ Empty :> add_i_1 :> n
  -- inv(i, n) /\ i+1 < n ==> inv(i+1, n)
  impl1 <- impliesPred sym conj0 inv_add_i_1_n
  le_0_i <- intLe sym zero i
  lt_i_n <- intLt sym i n
  conj1 <- andPred sym le_0_i lt_i_n
  -- inv(i, n) ==> 0 <= i /\ i < n
  impl2 <- impliesPred sym inv_i_n conj1

  -- inv(i, n) /\ not (i + 1 < n) ==> i + 1 == n
  not_lt_add_i_1_n <- notPred sym lt_add_i_1_n
  conj2 <- andPred sym inv_i_n not_lt_add_i_1_n
  eq_add_i_1_n <- intEq sym add_i_1 n
  impl3 <- impliesPred sym conj2 eq_add_i_1_n
  impl4 <- notPred sym impl3

  CVC5.runCVC5InOverride sym logData [impl4] $ \res -> isSat res @? "sat"

  subst <- CVC5.runCVC5SyGuS sym logData [SomeSymFn inv] [impl0, impl1, impl2] >>= \case
    Sat res -> return res
    Unsat{} -> fail "Infeasible"
    Unknown -> fail "Fail"

  impl5 <- substituteSymFns sym subst impl4
  CVC5.runCVC5InOverride sym logData [impl5] $ \res -> isUnsat res @? "unsat"

  Z3.runZ3InOverride sym logData [impl4] $ \res -> isSat res @? "sat"

  subst' <- Z3.runZ3Horn sym logData [SomeSymFn inv] [impl0, impl1, impl2] >>= \case
    Sat res -> return res
    Unsat{} -> fail "Infeasible"
    Unknown -> fail "Fail"

  impl5' <- substituteSymFns sym subst' impl4
  Z3.runZ3InOverride sym logData [impl5'] $ \res -> isUnsat res @? "unsat"

bvTest :: TestTree
bvTest = testCase "bv test" $ withSym FloatIEEERepr $ \sym -> do
  inv <- freshTotalUninterpFn sym (safeSymbol "inv") knownRepr knownRepr
  i <- freshConstant sym (safeSymbol "i") $ BaseBVRepr $ knownNat @64
  n <- freshConstant sym (safeSymbol "n") knownRepr
  zero <- bvLit sym knownNat $ BV.zero knownNat
  one <- bvLit sym knownNat $ BV.one knownNat
  ult_1_n <- bvUlt sym one n
  inv_0_n <- applySymFn sym inv $ Empty :> zero :> n
  -- 1 < n ==> inv(0, n)
  impl0 <- impliesPred sym ult_1_n inv_0_n
  inv_i_n <- applySymFn sym inv $ Empty :> i :> n
  add_i_1 <- bvAdd sym i one
  ult_add_i_1_n <- bvUlt sym add_i_1 n
  conj0 <- andPred sym inv_i_n ult_add_i_1_n
  inv_add_i_1_n <- applySymFn sym inv $ Empty :> add_i_1 :> n
  -- inv(i, n) /\ i+1 < n ==> inv(i+1, n)
  impl1 <- impliesPred sym conj0 inv_add_i_1_n
  ule_0_i <- bvUle sym zero i -- trivially true, here for similarity with int test
  ult_i_n <- bvUlt sym i n
  conj1 <- andPred sym ule_0_i ult_i_n
  -- inv(i, n) ==> 0 <= i /\ i < n
  impl2 <- impliesPred sym inv_i_n conj1

  -- inv(i, n) /\ not (i + 1 < n) ==> i + 1 == n
  not_ult_add_i_1_n <- notPred sym ult_add_i_1_n
  conj2 <- andPred sym inv_i_n not_ult_add_i_1_n
  eq_add_i_1_n <- bvEq sym add_i_1 n
  impl3 <- impliesPred sym conj2 eq_add_i_1_n
  impl4 <- notPred sym impl3

  CVC5.runCVC5InOverride sym logData [impl4] $ \res -> isSat res @? "sat"

  subst <- CVC5.runCVC5SyGuS sym logData [SomeSymFn inv] [impl0, impl1, impl2] >>= \case
    Sat res -> return res
    Unsat{} -> fail "Infeasible"
    Unknown -> fail "Fail"

  impl5 <- substituteSymFns sym subst impl4
  CVC5.runCVC5InOverride sym logData [impl5] $ \res -> isUnsat res @? "unsat"

main :: IO ()
main = defaultMain $ testGroup "Tests" $
  [ intTest
  , bvTest
  ]

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

import           ProbeSolvers
import           Test.Tasty
import           Test.Tasty.ExpectedFailure
import           Test.Tasty.HUnit

import           Data.Maybe
import           System.Environment

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Context
import           Data.Parameterized.Map (MapF)
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

intProblem :: IsSymExprBuilder sym => sym -> IO ([SomeSymFn sym], [Pred sym], Pred sym)
intProblem sym = do
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
  impl3 <- notPred sym =<< impliesPred sym conj2 eq_add_i_1_n

  return ([SomeSymFn inv], [impl0, impl1, impl2], impl3)

bvProblem :: IsSymExprBuilder sym => sym -> IO ([SomeSymFn sym], [Pred sym], Pred sym)
bvProblem sym = do
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
  impl3 <- notPred sym =<< impliesPred sym conj2 eq_add_i_1_n

  return ([SomeSymFn inv], [impl0, impl1, impl2], impl3)

synthesis_test ::
  String ->
  (forall sym . IsSymExprBuilder sym => sym -> IO ([SomeSymFn sym], [Pred sym], Pred sym)) ->
  String ->
  (forall sym t fs .
    sym ~ SimpleExprBuilder t fs =>
    sym ->
    LogData ->
    [SomeSymFn sym] ->
    [BoolExpr t] ->
    IO (SatResult (MapF (SymFnWrapper sym) (SymFnWrapper sym)) ())) ->
  (forall t fs a .
    SimpleExprBuilder t fs ->
    LogData ->
    [BoolExpr t] ->
    (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) () -> IO a) ->
    IO a) ->
  TestTree
synthesis_test test_name synthesis_problem solver_name run_solver_synthesis run_solver_in_override =
  testCase (test_name ++ " " ++ solver_name ++ " test") $ withSym FloatIEEERepr $ \sym -> do
    (synth_fns, constraints, goal) <- synthesis_problem sym

    run_solver_in_override sym logData [goal] $ \res -> isSat res @? "sat"

    subst <- run_solver_synthesis sym logData synth_fns constraints >>= \case
      Sat res -> return res
      Unsat{} -> fail "Infeasible"
      Unknown -> fail "Fail"

    goal' <- substituteSymFns sym subst goal
    run_solver_in_override sym logData [goal'] $ \res -> isUnsat res @? "unsat"

main :: IO ()
main = do
  testLevel <- TestLevel . fromMaybe "0" <$> lookupEnv "CI_TEST_LEVEL"
  let solverNames = map SolverName [ "cvc5", "z3" ]
  solvers <- reportSolverVersions testLevel id
    =<< (zip solverNames <$> mapM getSolverVersion solverNames)
  let skipPre4_8_9 why =
        let shouldSkip = case lookup (SolverName "z3") solvers of
              Just (SolverVersion v) -> any (`elem` [ "4.8.8" ]) $ words v
              Nothing -> True
        in if shouldSkip then expectFailBecause why else id
      failureZ3 = "failure with older Z3 versions; upgrade to at least 4.8.9"
  defaultMain $ testGroup "Tests" $
    [ synthesis_test "int" intProblem "cvc5" CVC5.runCVC5SyGuS CVC5.runCVC5InOverride
    , skipPre4_8_9 failureZ3 $ synthesis_test "int" intProblem "z3" Z3.runZ3Horn Z3.runZ3InOverride
    , synthesis_test "bv" bvProblem "cvc5" CVC5.runCVC5SyGuS CVC5.runCVC5InOverride
    ]

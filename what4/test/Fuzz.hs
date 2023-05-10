{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

import           Test.Tasty
import           Test.Tasty.HUnit

import qualified Data.BitVector.Sized as BV

import           Data.Parameterized.Context
import           Data.Parameterized.Nonce

import           What4.Concrete
import           What4.Config
import           What4.Expr
import           What4.Expr.Fuzz
import           What4.Interface
import qualified What4.Solver.CVC5 as CVC5
import qualified What4.Solver.Z3 as Z3

type SimpleExprBuilder t fs = ExprBuilder t EmptyExprBuilderState fs

withSym :: FloatModeRepr fm -> (forall t . SimpleExprBuilder t (Flags fm) -> IO a) -> IO a
withSym float_mode action = withIONonceGenerator $ \gen -> do
  sym <- newExprBuilder float_mode EmptyExprBuilderState gen
  extendConfig CVC5.cvc5Options (getConfiguration sym)
  extendConfig Z3.z3Options (getConfiguration sym)
  action sym

test_bvult_i_n :: TestTree
test_bvult_i_n = testCase "test (bvult i n)" $ withSym FloatIEEERepr $ \sym -> do
  i <- freshConstant sym (safeSymbol "i") $ BaseBVRepr $ knownNat @64
  n <- freshConstant sym (safeSymbol "n") knownRepr
  ult_i_n <- bvUlt sym i n

  is_not_sat <- fst <$> evaluateExpr sym 10 1000 ult_i_n
  False @=? is_not_sat

  is_sat <- fst <$> evaluateExpr sym 30 1000 ult_i_n
  True @=? is_sat

test_lt_i_n :: TestTree
test_lt_i_n = testCase "test (< i n)" $ withSym FloatIEEERepr $ \sym -> do
  i <- freshConstant sym (safeSymbol "i") knownRepr
  n <- freshConstant sym (safeSymbol "n") knownRepr
  lt_i_n <- intLt sym i n

  is_not_sat <- fst <$> evaluateExpr sym 25 1000 lt_i_n
  False @=? is_not_sat

  is_sat <- fst <$> evaluateExpr sym 10 1000 lt_i_n
  True @=? is_sat

test_uninterp_f_i_n :: TestTree
test_uninterp_f_i_n = testCase "test (= (f i n) (f i n))" $ withSym FloatIEEERepr $ \sym -> do
  f <- freshTotalUninterpFn sym (safeSymbol "f") knownRepr knownRepr
  i <- freshConstant sym (safeSymbol "i") $ BaseBVRepr $ knownNat @64
  n <- freshConstant sym (safeSymbol "n") $ BaseBVRepr $ knownNat @64

  f_i_n <- applySymFn sym f $ Empty :> i :> n
  f_i_n' <- applySymFn sym f $ Empty :> i :> n
  eq_f_i_n_f_i_n' <- eqPred sym f_i_n f_i_n'

  is_sat <- fst <$> evaluateExpr sym 10 1000 eq_f_i_n_f_i_n'
  True @=? is_sat

test_uninterp_f_i_n_bvmul_bvshl_eq :: TestTree
test_uninterp_f_i_n_bvmul_bvshl_eq = testCase "test (= (bvmul (f i n) 0x2) (bvshl (f i n) 0x1))" $ withSym FloatIEEERepr $ \sym -> do
  f <- freshTotalUninterpFn sym (safeSymbol "f") knownRepr $ BaseBVRepr $ knownNat @64
  i <- freshConstant sym (safeSymbol "i") $ BaseBVRepr $ knownNat @64
  n <- freshConstant sym (safeSymbol "n") $ BaseBVRepr $ knownNat @64

  f_i_n <- applySymFn sym f $ Empty :> i :> n
  bvmul_f_i_n_2 <- bvMul sym f_i_n =<< bvLit sym knownNat (BV.mkBV knownNat 2)
  bvshl_f_i_n_2 <- bvShl sym f_i_n =<< bvLit sym knownNat (BV.mkBV knownNat 1)
  eq_bvmul_f_i_n_2_bvshl_f_i_n_2 <- bvEq sym bvmul_f_i_n_2 bvshl_f_i_n_2

  Nothing @=? asConcrete eq_bvmul_f_i_n_2_bvshl_f_i_n_2

  eq_bvmul_f_i_n_2_bvshl_f_i_n_2_simplified <- simplifyExpr sym 10 1000 2 eq_bvmul_f_i_n_2_bvshl_f_i_n_2
  Just True @=? fromConcreteBool <$> asConcrete eq_bvmul_f_i_n_2_bvshl_f_i_n_2_simplified

main :: IO ()
main = do
  defaultMain $ testGroup "Tests"
    [ test_bvult_i_n
    , test_lt_i_n
    , test_uninterp_f_i_n
    , test_uninterp_f_i_n_bvmul_bvshl_eq
    ]

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}

import Control.Exception ( displayException, try, SomeException )
import Control.Lens (folded)
import Control.Monad ( forM, unless, void )
import Control.Monad.Except ( runExceptT )
import Data.BitVector.Sized ( mkBV )
import Data.Char ( toLower )
import System.Exit ( ExitCode(..) )
import System.Process ( readProcessWithExitCode )

import Test.Tasty
import Test.Tasty.HUnit

import Data.Parameterized.Nonce
import Data.Parameterized.Some

import What4.Config
import What4.Interface
import What4.Expr
import What4.Solver
import What4.Protocol.VerilogWriter

data State t = State

allAdapters :: [SolverAdapter State]
allAdapters =
  [ cvc4Adapter
  , yicesAdapter
  , z3Adapter
  , boolectorAdapter
  , externalABCAdapter
#ifdef TEST_STP
  , stpAdapter
#endif
  ] <> drealAdpt

drealAdpt :: [SolverAdapter State]
#ifdef TEST_DREAL
drealAdpt = [drealAdapter]
#else
drealAdpt = []
#endif


withSym :: SolverAdapter State -> (forall t . ExprBuilder t State (Flags FloatUninterpreted) -> IO a) -> IO a
withSym adpt pred_gen = withIONonceGenerator $ \gen ->
  do sym <- newExprBuilder FloatUninterpretedRepr State gen
     extendConfig (solver_adapter_config_options adpt) (getConfiguration sym)
     pred_gen sym

mkSmokeTest :: SolverAdapter State -> TestTree
mkSmokeTest adpt = testCase (solver_adapter_name adpt) $
  withSym adpt $ \sym ->
   do res <- smokeTest sym adpt
      case res of
        Nothing -> return ()
        Just ex -> fail $ displayException ex

nonlinearRealTest :: SolverAdapter State -> TestTree
nonlinearRealTest adpt = testCase (solver_adapter_name adpt) $
  withSym adpt $ \sym ->
    do x <- freshConstant sym (safeSymbol "a") BaseRealRepr
       y <- freshConstant sym (safeSymbol "b") BaseRealRepr

       xabs <- realAbs sym x

       x2 <- realMul sym x x

       x2_1 <- realAdd sym x2 =<< realLit sym 1
       x2_y <- realAdd sym x2 y

       p1 <- realLt sym x2_1 =<< realLit sym 0

       p2 <- realLe sym x2_y =<< realLit sym (-1)
       p3 <- realGe sym x2_y =<< realLit sym (-2)
       p4 <- realLe sym xabs =<< realLit sym 10

       -- asking if `x^2 < 0` should be unsat
       solver_adapter_check_sat adpt sym defaultLogData [p1] $ \case
           Unsat _ -> return ()
           Unknown -> fail "Solver returned UNKNOWN"
           Sat _ -> fail "Should be UNSAT!"

       -- asking to find `-2 <= x^2 + y <= -1` with `abs(x) <= 10`. Should find something.
       solver_adapter_check_sat adpt sym defaultLogData [p2,p3,p4] $ \case
           Unsat _ -> fail "Shoule be UNSAT!"
           Unknown -> fail "Solver returned UNKNOWN"
           Sat (eval,_bounds) ->
             do x' <- groundEval eval x
                abs x' <= 10 @? "correct abs(x) bound"

                x2_y' <- groundEval eval x2_y
                ((-2) <= x2_y' && x2_y' <= (-1)) @? "correct bounds"


mkQuickstartTest :: SolverAdapter State -> TestTree
mkQuickstartTest adpt = testCase (solver_adapter_name adpt) $
  withSym adpt $ \sym ->
    do -- Let's determine if the following formula is satisfiable:
       -- f(p, q, r) = (p | !q) & (q | r) & (!p | !r) & (!p | !q | r)

       -- First, declare fresh constants for each of the three variables p, q, r.
       p <- freshConstant sym (safeSymbol "p") BaseBoolRepr
       q <- freshConstant sym (safeSymbol "q") BaseBoolRepr
       r <- freshConstant sym (safeSymbol "r") BaseBoolRepr

       -- Next, create terms for the negation of p, q, and r.
       not_p <- notPred sym p
       not_q <- notPred sym q
       not_r <- notPred sym r

       -- Next, build up each clause of f individually.
       clause1 <- orPred sym p not_q
       clause2 <- orPred sym q r
       clause3 <- orPred sym not_p not_r
       clause4 <- orPred sym not_p =<< orPred sym not_q r

       -- Finally, create f out of the conjunction of all four clauses.
       f <- andPred sym clause1 =<<
            andPred sym clause2 =<<
            andPred sym clause3 clause4

       (p',q',r') <-
         solver_adapter_check_sat adpt sym defaultLogData [f] $ \case
           Unsat _ -> fail "Unsatisfiable"
           Unknown -> fail "Solver returned UNKNOWN"
           Sat (eval, _) ->
               do p' <- groundEval eval p
                  q' <- groundEval eval q
                  r' <- groundEval eval r
                  return (p',q',r')

       -- This is the unique satisfiable model
       p' == False @? "p value"
       q' == False @? "q value"
       r' == True  @? "r value"

       -- Compute a blocking predicate for the computed model
       bs <- forM [(p,p'),(q,q'),(r,r')] $ \(x,v) -> eqPred sym x (backendPred sym v)
       block <- notPred sym =<< andAllOf sym folded bs

       -- Ask if there is some other model
       solver_adapter_check_sat adpt sym defaultLogData [f,block] $ \case
           Unsat _ -> return ()
           Unknown -> fail "Solver returned UNKNOWN"
           Sat _   -> fail "Should be a unique model!"

verilogTest :: TestTree
verilogTest = testCase "verilogTest" $ withIONonceGenerator $ \gen ->
  do sym <- newExprBuilder FloatUninterpretedRepr State gen
     let w = knownNat @8
     x <- freshConstant sym (safeSymbol "x") (BaseBVRepr w)
     one <- bvLit sym w (mkBV w 1)
     add <- bvAdd sym x one
     r <- notPred sym =<< bvEq sym x add
     edoc <- runExceptT (exprsVerilog sym [] [Some r] "f")
     case edoc of
       Left err -> fail $ "Failed to translate to Verilog: " ++ err
       Right doc ->
         unless (show doc ++ "\n" == refDoc) $
           fail $ unlines [
                     "Unexpected output from Verilog translation:"
                    , show doc
                    , "instead of"
                    , refDoc
                    ]
  where
    refDoc = unlines [ "module f(x, out);"
                     , "  input [7:0] x;"
                     , "  wire [7:0] wr = 8'h1;"
                     , "  wire [7:0] wr_2 = wr * x;"
                     , "  wire [7:0] wr_3 = wr + wr_2;"
                     , "  wire wr_4 = wr_3 == x;"
                     , "  wire wr_5 = ! wr_4;"
                     , "  output out = wr_5;"
                     , "endmodule"
                     ]

getSolverVersion :: String -> IO String
getSolverVersion solver = do
  try (readProcessWithExitCode (toLower <$> solver) ["--version"] "") >>= \case
    Right (r,o,e) ->
      if r == ExitSuccess
      then let ol = lines o in
             return $ if null ol then (solver <> " v??") else head ol
      else return $ solver <> " version error: " <> show r <> " /;/ " <> e
    Left (err :: SomeException) -> return $ solver <> " invocation error: " <> show err


reportSolverVersions :: IO ()
reportSolverVersions = do putStrLn "SOLVER VERSIONS::"
                          void $ mapM rep allAdapters
  where rep a = let s = solver_adapter_name a in disp s =<< getSolverVersion s
        disp s v = putStrLn $ "  Solver " <> s <> " == " <> v


main :: IO ()
main = do
  reportSolverVersions
  defaultMain $
    localOption (mkTimeout (10 * 1000 * 1000)) $
    testGroup "AdapterTests"
    [ testGroup "SmokeTest" $ map mkSmokeTest allAdapters
    , testGroup "QuickStart" $ map mkQuickstartTest allAdapters
    , testGroup "nonlinear reals" $ map nonlinearRealTest
      -- NB: nonlinear arith expected to fail for STP and Boolector
      ([ cvc4Adapter, z3Adapter, yicesAdapter ] <> drealAdpt)
    , testGroup "Verilog" [verilogTest]
    ]

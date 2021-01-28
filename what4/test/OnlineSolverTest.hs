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

import           Control.Exception ( try, SomeException )
import           Control.Lens (folded)
import           Control.Monad ( forM, void )
import           Data.Char ( toLower )
import           Data.Proxy
import           System.Exit ( ExitCode(..) )
import           System.Process ( readProcessWithExitCode )

import           Test.Tasty
import           Test.Tasty.HUnit

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Nonce

import           What4.Config
import           What4.Interface
import           What4.Expr
import           What4.ProblemFeatures
import           What4.Solver
import           What4.Protocol.Online
import           What4.Protocol.SMTWriter
import qualified What4.Protocol.SMTLib2 as SMT2
import qualified What4.Solver.Yices as Yices

data State t = State

allOnlineSolvers :: [(String, AnOnlineSolver, ProblemFeatures, [ConfigDesc])]
allOnlineSolvers =
  [ ("Z3", AnOnlineSolver @(SMT2.Writer Z3) Proxy, z3Features, z3Options)
  , ("CVC4",  AnOnlineSolver @(SMT2.Writer CVC4) Proxy, cvc4Features, cvc4Options)
  , ("Yices", AnOnlineSolver @Yices.Connection Proxy, yicesDefaultFeatures, yicesOptions)
  , ("Boolector", AnOnlineSolver @(SMT2.Writer Boolector) Proxy, boolectorFeatures, boolectorOptions)
#ifdef TEST_STP
  , ("STP", AnOnlineSolver @(SMT2.Writer STP) Proxy, stpFeatures, stpOptions)
#endif
  ]

mkSmokeTest :: (String, AnOnlineSolver, ProblemFeatures, [ConfigDesc]) -> TestTree
mkSmokeTest (nm, AnOnlineSolver (Proxy :: Proxy s), features, opts) = testCase nm $
  withIONonceGenerator $ \gen ->
  do sym <- newExprBuilder FloatUninterpretedRepr State gen
     extendConfig opts (getConfiguration sym)
     proc <- startSolverProcess @s features Nothing sym
     let conn = solverConn proc
     inNewFrame proc $
       do assume conn (falsePred sym)
          check proc "smoke test" >>= \case
            Unknown -> fail "Solver returned UNKNOWN"
            Sat _ -> fail "Should be UNSAT"
            Unsat _ -> return ()


----------------------------------------------------------------------

mkFormula1 :: IsSymExprBuilder sym
          => sym
          -> IO ( SymExpr sym BaseBoolType
                , SymExpr sym BaseBoolType
                , SymExpr sym BaseBoolType
                , SymExpr sym BaseBoolType
                )
mkFormula1 sym = do
     -- Let's determine if the following formula is satisfiable:
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

     return (p,q,r,f)

-- Checks that the only valid model for Formula1 was found, and then
-- returns an expression that (as an assumption) disallows that model.
checkFormula1Model :: (IsExprBuilder sym, SymExpr sym ~ Expr t)
                   => sym
                   -> Expr t BaseBoolType
                   -> Expr t BaseBoolType
                   -> Expr t BaseBoolType
                   -> GroundEvalFn t
                   -> IO (SymExpr sym BaseBoolType)
checkFormula1Model sym p q r eval =
  do p' <- groundEval eval p
     q' <- groundEval eval q
     r' <- groundEval eval r

     -- This is the unique satisfiable model
     p' == False @? "p value"
     q' == False @? "q value"
     r' == True  @? "r value"

     -- Return an assumption that blocks this model
     bs <- forM [(p,p'),(q,q'),(r,r')] $ \(x,v) -> eqPred sym x (backendPred sym v)
     block <- notPred sym =<< andAllOf sym folded bs

     return block


-- Solve Formula1 using a frame (push/pop) for each of the good and
-- bad cases
quickstartTest :: (String, AnOnlineSolver, ProblemFeatures, [ConfigDesc]) -> TestTree
quickstartTest (nm, AnOnlineSolver (Proxy :: Proxy s), features, opts) = testCaseSteps nm $ \step ->
  withIONonceGenerator $ \gen ->
  do sym <- newExprBuilder FloatUninterpretedRepr State gen
     extendConfig opts (getConfiguration sym)

     (p,q,r,f) <- mkFormula1 sym

     step "Start Solver"
     proc <- startSolverProcess @s features Nothing sym
     let conn = solverConn proc

     -- Check that formula f is satisfiable, and get the values from
     -- the model that satisifies it

     step "Check Satisfiability"
     block <- inNewFrame proc $
       do assume conn f
          res <- check proc "framed formula1 satisfiable"
          case res of
            Unsat _ -> fail "Unsatisfiable"
            Unknown -> fail "Solver returned UNKNOWN"
            Sat _ ->
              checkFormula1Model sym p q r =<< getModel proc

     -- Now check that the formula is unsatisfiable when the blocking
     -- predicate is added.  Re-use the existing solver connection

     step "Check Unsatisfiable"
     inNewFrame proc $
       do assume conn f
          assume conn block
          res <- check proc "framed formula1 unsatisfiable"
          case res of
            Unsat _ -> return ()
            Unknown -> fail "Solver returned UNKNOWN"
            Sat _   -> fail "Should be a unique model!"



-- Solve Formula1 directly, with a solver reset between good and bad cases
quickstartTestAlt :: (String, AnOnlineSolver, ProblemFeatures, [ConfigDesc]) -> TestTree
quickstartTestAlt (nm, AnOnlineSolver (Proxy :: Proxy s), features, opts) = testCaseSteps nm $ \step ->
  withIONonceGenerator $ \gen ->
  do sym <- newExprBuilder FloatUninterpretedRepr State gen
     extendConfig opts (getConfiguration sym)

     (p,q,r,f) <- mkFormula1 sym

     step "Start Solver"
     proc <- startSolverProcess @s features Nothing sym
     let conn = solverConn proc

     -- Check that formula f is satisfiable, and get the values from
     -- the model that satisifies it

     step "Check Satisfiability"
     block <-
       do assume conn f
          res <- check proc "direct formula1 satisfiable"
          case res of
            Unsat _ -> fail "Unsatisfiable"
            Unknown -> fail "Solver returned UNKNOWN"
            Sat _ ->
              checkFormula1Model sym p q r =<< getModel proc

     -- Now check that the formula is unsatisfiable when the blocking
     -- predicate is added.  Re-use the existing solver connection

     reset proc

     step "Check Unsatisfiable"
     assume conn f
     assume conn block
     res <- check proc "direct formula1 unsatisfiable"
     case res of
       Unsat _ -> return ()
       Unknown -> fail "Solver returned UNKNOWN"
       Sat _   -> fail "Should be a unique model!"

----------------------------------------------------------------------



getSolverVersion :: String -> IO String
getSolverVersion solver =
  try (readProcessWithExitCode (toLower <$> solver) ["--version"] "") >>= \case
    Right (r,o,e) ->
      if r == ExitSuccess
      then let ol = lines o in
             return $ if null ol then (solver <> " v??") else head ol
      else return $ solver <> " version error: " <> show r <> " /;/ " <> e
    Left (err :: SomeException) -> return $ solver <> " invocation error: " <> show err


reportSolverVersions :: IO ()
reportSolverVersions = do putStrLn "SOLVER VERSIONS::"
                          void $ mapM rep allOnlineSolvers
  where rep (s,_,_,_) = disp s =<< getSolverVersion s
        disp s v = putStrLn $ "  Solver " <> s <> " == " <> v


main :: IO ()
main = do
  reportSolverVersions
  defaultMain $
    localOption (mkTimeout (10 * 1000 * 1000)) $
    testGroup "OnlineSolverTests"
    [
      testGroup "SmokeTest" $ map mkSmokeTest allOnlineSolvers
    , testGroup "QuickStart Framed" $ map quickstartTest allOnlineSolvers
    , testGroup "QuickStart Direct" $ map quickstartTestAlt allOnlineSolvers
    ]

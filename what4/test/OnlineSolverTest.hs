{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}

import           Control.Concurrent ( threadDelay )
import           Control.Concurrent.Async ( race )
import           Control.Exception ( try, SomeException )
import           Control.Lens (folded)
import           Control.Monad ( forM, void )
import           Control.Monad.Catch ( MonadMask )
import           Control.Monad.IO.Class ( MonadIO )
import           Data.Char ( toLower )
import           Data.Either ( isLeft, isRight )
import qualified Data.List as L
import           Data.Maybe ( fromMaybe )
import           Data.Metrology ( (%), (#), (|<=|), (|*), (|<|), qApprox )
import           Data.Metrology.SI ( Time, milli, micro, nano, Second(..) )
import           Data.Metrology.Show ()
import           Data.Proxy
import qualified Prettyprinter as PP
import           System.Clock
import           System.Exit ( ExitCode(..) )
import           System.Process ( readProcessWithExitCode )

import           Test.Tasty
import qualified Test.Tasty.Checklist as TCL
import           Test.Tasty.ExpectedFailure
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

type SolverTestData = (String, AnOnlineSolver, ProblemFeatures, [ConfigDesc], Maybe (ConfigOption BaseIntegerType))

allOnlineSolvers :: [SolverTestData]
allOnlineSolvers =
  [ ("Z3", AnOnlineSolver @(SMT2.Writer Z3) Proxy, z3Features, z3Options, Just z3Timeout)
  , ("CVC4",  AnOnlineSolver @(SMT2.Writer CVC4) Proxy, cvc4Features, cvc4Options, Just cvc4Timeout)
  , ("Yices", AnOnlineSolver @Yices.Connection Proxy, yicesDefaultFeatures, yicesOptions, Just yicesGoalTimeout)
  , ("Boolector", AnOnlineSolver @(SMT2.Writer Boolector) Proxy, boolectorFeatures, boolectorOptions, Nothing)
#ifdef TEST_STP
  , ("STP", AnOnlineSolver @(SMT2.Writer STP) Proxy, stpFeatures, stpOptions, Nothing)
#endif
  ]

testSolverName (nm,_,_,_,_) = nm

instance TCL.TestShow [PP.Doc ann] where
  testShow = L.intercalate ", " . fmap show

-- The smoke test is a simple test to ensure that the solver can be
-- queried for a computable result and that the result can be obtained
-- in a reasonably quick amount of time with no cancel or timeouts
-- considerations.
mkSmokeTest :: SolverTestData -> TestTree
mkSmokeTest (nm, AnOnlineSolver (Proxy :: Proxy s), features, opts, timeoutOpt) = testCase nm $
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


-- Solve (the relatively simple) Formula1 using either frames
-- (push/pop) for each of the good and bad cases or else no frames and
-- resetting the solver between cases
quickstartTest :: Bool -> SolverTestData -> TestTree
quickstartTest useFrames (nm, AnOnlineSolver (Proxy :: Proxy s), features, opts, _timeoutOpt) =
  testCaseSteps nm $ \step ->
  withIONonceGenerator $ \gen ->
  do sym <- newExprBuilder FloatUninterpretedRepr State gen
     extendConfig opts (getConfiguration sym)

     (p,q,r,f) <- mkFormula1 sym

     step "Start Solver"
     proc <- startSolverProcess @s features Nothing sym
     let conn = solverConn proc

     -- helpers for operating framed v.s. non-framed testing

     let startOnlineCheck :: (MonadMask m, MonadIO m, SMTReadWriter solver) => SolverProcess scope solver -> m b -> m b
         startOnlineCheck = if useFrames then inNewFrame else passThru
         resetOnlineCheck = if useFrames then doNothing  else reset
         doNothing = const $ return ()
         passThru _ op = op
         checkType = if useFrames then "framed" else "direct"

     -- Check that formula f is satisfiable, and get the values from
     -- the model that satisifies it

     step "Check Satisfiability"
     block <- startOnlineCheck proc $
       do assume conn f
          res <- check proc $ checkType <> " formula1 satisfiable"
          case res of
            Unsat _ -> fail "Unsatisfiable"
            Unknown -> fail "Solver returned UNKNOWN"
            Sat _ ->
              checkFormula1Model sym p q r =<< getModel proc

     -- Now check that the formula is unsatisfiable when the blocking
     -- predicate is added.  Re-use the existing solver connection

     resetOnlineCheck proc

     step "Check Unsatisfiable"
     startOnlineCheck proc  $
       do assume conn f
          assume conn block
          res <- check proc $ checkType <> " formula1 unsatisfiable"
          case res of
            Unsat _ -> return ()
            Unknown -> fail "Solver returned UNKNOWN"
            Sat _   -> fail "Should be a unique model!"


----------------------------------------------------------------------

-- This constructs a What4 formula that takes the solvers a
-- non-trivial amount of time to find a solution for.  This is used
-- for running tests that are expected to be interrupted by a timeout,
-- although this formula should run to completion if unrestricted.
mkFormula2 :: IsSymExprBuilder sym => sym -> IO (Pred sym)
mkFormula2 sym = do
     p <- freshConstant sym (safeSymbol "p8") (BaseBVRepr (knownNat @8))
     q <- freshConstant sym (safeSymbol "q8") (BaseBVRepr (knownNat @8))
     r <- freshConstant sym (safeSymbol "q8") (BaseBVRepr (knownNat @8))
     zeroBV <- bvLit sym (knownNat @8) (BV.zero (knownNat))

     let bvGCD n a b = do
           isZero <- bvEq sym zeroBV b
           recurs <- if n == 0 then return a
                     else bvGCD (n-1) b =<< (bvUrem sym a b)
           bvIte sym isZero a recurs

     -- String together some symbolic GCD calculations to make
     -- something that the solver takes a while to check.  The goal
     -- here is something long enough that we can test various
     -- timeouts.
     gcd1 <- bvGCD (256 :: Int) p r
     gcd2 <- bvGCD (256 :: Int) q r
     gcdRes <- bvGCD (256 :: Int) gcd1 gcd2

     chk1 <- bvUle sym gcdRes p
     chk2 <- bvUle sym gcdRes q
     -- chk3 <- bvNe sym gcdRes zero
     -- chk4 <- bvEq sym gcdRes zero
     -- andPred sym chk1 =<< andPred sym chk2 chk3
     andAllOf sym folded [chk1, chk2] -- , chk3, chk4]

-- Attempt to solve an extensive formula (using frames: push/pop) that
-- should exceed the solver goal-timeout.  This can be used to verify
-- that the goal-timeout is realized and that the solver is useable
-- for a goal _after_ the goal-timeout was reached.
longTimeTest :: SolverTestData -> Maybe Time -> IO Bool
longTimeTest (nm, AnOnlineSolver (Proxy :: Proxy s), features, opts, mb'timeoutOpt) goal_tmo =
  TCL.withChecklist "timer tests" $
  withIONonceGenerator $ \gen ->
  do sym <- newExprBuilder FloatUninterpretedRepr State gen
     extendConfig opts (getConfiguration sym)

     case goal_tmo of
       Nothing -> return ()
       Just t -> case mb'timeoutOpt of
         Nothing -> error $ "No goal timeout option for backend solver " <> nm
         Just timeoutOpt -> do
           tmOpt <- getOptionSetting timeoutOpt $ getConfiguration sym
           warnings <- setOpt tmOpt $ floor (t # milli Second)
           TCL.check "timer option set" null warnings

     f <- mkFormula2 sym

     proc' <- startSolverProcess @s features Nothing sym
     let proc = maybe proc'
           (\t -> proc' {
               solverGoalTimeout = SolverGoalTimeout $ floor (t # micro Second)
               }
           ) goal_tmo
     let conn = solverConn proc

     -- Check that formula f is satisfiable, and get the values from
     -- the model that satisifies it

     do assume conn f
        check proc "direct formula2 satisfiable" >>= \case
          Unsat _ -> fail "Unsatisfiable"
          Unknown -> return False  -- how a solver indicates a timeout
          Sat _ -> return True
--            checkFormula1Model sym p q r =<< getModel proc


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
reportSolverVersions = do putStrLn "SOLVER SELF-REPORTED VERSIONS::"
                          void $ mapM rep allOnlineSolvers
  where rep testsolver = let s = testSolverName testsolver in disp s =<< getSolverVersion s
        disp s v = putStrLn $ "  Solver " <> s <> " -> " <> v


main :: IO ()
main = do
  reportSolverVersions
  defaultMain $
    -- localOption (mkTimeout (10 * 1000 * 1000)) $
    testGroup "OnlineSolverTests"
    [
      testGroup "SmokeTest" $ map mkSmokeTest allOnlineSolvers
    , testGroup "QuickStart Framed" $ map (quickstartTest True)  allOnlineSolvers
    , testGroup "QuickStart Direct" $ map (quickstartTest False) allOnlineSolvers
    , timeoutTests
    ]

-- Test the effects of general timeouts on solver proofs
--
-- n.b. Approximate times obviously highly variant based on test
-- machine, etc.  As long as they run consistently longer than the
-- useable threshold the tests should perform as expected.

timeoutTests :: TestTree
timeoutTests =
  let
      -- Amount of time to use for timeouts in testing: can be edited
      -- to adjust the timeout threshold needed.  This should be large
      -- enough to allow the solver to engage on the task, but smaller
      -- than the expected completion time by enough that the timeout
      -- will halt the test before it completes.
      --
      -- If the timeout is too short there is the risk that it's not a
      -- valid timeout test because of:
      --
      --   1. machine speed variance
      --   2. scheduling and solver startup variance
      --   3. timer resolution and timeout-driven scheduling
      --
      -- If the timeout value is too large, then the solver may
      -- complete the proof more quickly than the timeout will fire.
      -- Also, people get bored.
      --
      -- This value should also be <= 60% of useableTimeThreshold to
      -- ensure that the solver runs for a siginificantly longer
      -- period than the test timeout will be set to.
      --
      -- This value can be adjusted by the developer as needed to
      -- reasonably validate timeout testing subject to the above
      -- considerations.
      testTimeout = 100 % milli Second

      -- Solvers must run for at least this amount of time to be
      -- useable for timeout tests.  The test timeout value is
      -- determined by 'testTimeout', but if the solver does not run
      -- for at least the 'useableTimeThreshold' then the test result
      -- is likely to be indeterminate due to scheduling and timeout
      -- handling variance.
      --
      -- This value is only used for validating individual tests and
      -- does not control how long the actual tests run.
      --
      -- This value can be adjusted by the developer for cause.
      useableTimeThreshold = 250 % milli Second :: Time
      -- useableTimeThreshold = 4 % Second :: Time

      -- This is empirical data from previous runs of the "Test itself
      -- is valid and completes" test case; this data is used to guide
      -- the current evaluation; times here will be compared to the
      -- 'useableTimeThreshold' to verify that tests can be accurately
      -- run.  This table may need to be updated periodically by the
      -- developer as solvers, What4 formulation, and machine speeds
      -- evolve.
      approxTestTimes :: [ (String, Time) ]
      approxTestTimes = [ ("Z3",         2.27 % Second)    -- Z3 4.8.10
                        , ("CVC4",       6.37 % Second)    -- CVC4 1.8
                        , ("Yices",      2.66 % Second)    -- Yices 2.6.1
                        , ("Boolector",  6.56 % Second)    -- Boolector 3.2.1
                        , ("STP",        0 % Second)       -- unknown yet
                        ]

      -- This is the acceptable delta variation in time between the
      -- times in the approxTestTimes above and the actual test times.
      -- If difference between the two exceeds this amount then it
      -- represents a significant variation that should be attended
      -- to; either the values in the approxTestTimes needs to be
      -- ujpdated to account for evolved functionality or the test
      -- formulas should be updated to ensure that reasonable timeout
      -- testing can be performed (or there is a significant
      -- performance regression or unexpected improvement in What4).
      --
      -- Note that when this test executable is run solo, a delta
      -- value of ~ 0.5 Second is sufficient, but when *all* test
      -- executables are run in parallel via `cabal test`, there seems
      -- to be a much larger variation in testing times.  This may be
      -- due to increased CPU load or scheduling variance due multiple
      -- parallel running multiple tests.
      --
      acceptableTimeDelta = 800 % milli Second :: Time  -- solo
      -- acceptableTimeDelta = 2.2 % Second :: Time   -- parallelized

      --------------------------------------------------
      -- end of expected developer-adjustments above  --
      --------------------------------------------------

      mkTimeoutTests s =
        let historical = fromMaybe (0.0 % Second) $ lookup (testSolverName s) approxTestTimes
        in testGroup (testSolverName s)
           [
             testCase ("Test itself is valid and completes (" <> show historical <> ")") $ do
               -- Verify that the solver will run to completion for
               -- this test if there is no time limit, and also that
               -- the approxTestTimes historical time is reasonably
               -- close to the actual time taken for this test.
               start <- getTime Monotonic
               longTimeTest s Nothing @? "valid test"
               finish <- getTime Monotonic
               let deltaT = (fromInteger $ toNanoSecs $ diffTimeSpec start finish) % nano Second :: Time
               assertBool
                 ("actual duration of " <> show deltaT <> " is significantly different than expected")
                 $ qApprox acceptableTimeDelta deltaT historical

           , let maybeRunTest = if useableTimeThreshold |<| historical
                                then id
                                else ignoreTestBecause $ unwords
                                     [ "solver runs test faster than "
                                     , "reasonable timing threshold;"
                                     , "skipping"
                                     ]
             in maybeRunTest $ testCase "Test runs past timeout" $ do
               rslt <- race
                       (threadDelay (floor $ useableTimeThreshold # micro Second))
                       (longTimeTest s Nothing)
               isLeft rslt @? "solver is to fast for valid timeout testing"

           -- Verify that specifying a goal-timeout will stop once
           -- that timeout is reached (i.e. before the race timeout here).
           , testCase "Test with goal timeout" $ do
               rslt <- race
                       (threadDelay (floor $ useableTimeThreshold # micro Second))
                       (longTimeTest s (Just testTimeout))
               isRight rslt @? "solver goal timeout didn't occur"
               assertEqual "solver didn't timeout on goal" (Right False) rslt
               -- TODO: ensure that the solver process is no longer using CPU time.
           ]

  in testGroup "Timeout Tests" $
     [
       testCase "valid test timeout" $
       -- Verify that the user-defineable 'testTimeout' is a
       -- reasonable value.  If this fails, ignore all other test
       -- results and modify the 'testTimeout'.
       testTimeout |<=| useableTimeThreshold |* 0.60 @?
       "test timeout too large"

     ] <> map mkTimeoutTests allOnlineSolvers

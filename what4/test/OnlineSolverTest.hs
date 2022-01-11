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
{-# OPTIONS_GHC -fno-warn-orphans #-} -- for TestShow instance

import           Control.Concurrent ( threadDelay )
import           Control.Concurrent.Async ( race )
import           Control.Lens (folded)
import           Control.Monad ( forM )
import           Control.Monad.Catch ( MonadMask )
import           Control.Monad.IO.Class ( MonadIO )
import           Data.Either ( isLeft, isRight )
import qualified Data.List as L
import           Data.Maybe ( fromMaybe )
import           Data.Metrology ( (%), (#), (|<=|), (|*), (|<|), (|+|), qApprox )
import           Data.Metrology.SI ( Time, milli, micro, nano, Second(..) )
import           Data.Metrology.Show ()
import           Data.Proxy
import qualified Prettyprinter as PP
import           System.Clock
import           System.Environment ( lookupEnv )

import           ProbeSolvers
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

type SolverTestData = (SolverName, AnOnlineSolver, ProblemFeatures, [ConfigDesc], Maybe (ConfigOption BaseIntegerType))

allOnlineSolvers :: [SolverTestData]
allOnlineSolvers =
  [ (SolverName "Z3"
    , AnOnlineSolver @(SMT2.Writer Z3) Proxy, z3Features, z3Options, Just z3Timeout)
  , (SolverName "CVC4"
    ,  AnOnlineSolver @(SMT2.Writer CVC4) Proxy, cvc4Features, cvc4Options, Just cvc4Timeout)
  , (SolverName "Yices"
    , AnOnlineSolver @Yices.Connection Proxy, yicesDefaultFeatures, yicesOptions, Just yicesGoalTimeout)
  , (SolverName "Boolector"
    , AnOnlineSolver @(SMT2.Writer Boolector) Proxy, boolectorFeatures, boolectorOptions, Just boolectorTimeout)
#ifdef TEST_STP
  , (SolverName "STP"
    , AnOnlineSolver @(SMT2.Writer STP) Proxy, stpFeatures, stpOptions, Just stpTimeout)
#endif
  ]

testSolverName :: SolverTestData -> SolverName
testSolverName (nm,_,_,_,_) = nm

instance TCL.TestShow [PP.Doc ann] where
  testShow = L.intercalate ", " . fmap show

-- The smoke test is a simple test to ensure that the solver can be
-- queried for a computable result and that the result can be obtained
-- in a reasonably quick amount of time with no cancel or timeouts
-- considerations.
mkSmokeTest :: (SolverTestData, SolverVersion) -> TestTree
mkSmokeTest ((SolverName nm, AnOnlineSolver (_ :: Proxy s), features, opts, _), _) =
  testCase nm $ withIONonceGenerator $ \gen ->
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
quickstartTest :: Bool -> (SolverTestData,SolverVersion) -> TestTree
quickstartTest useFrames ((SolverName nm, AnOnlineSolver (Proxy :: Proxy s), features, opts, _timeoutOpt),_) =
  let wrap = if nm == "STP"
             then ignoreTestBecause "STP cannot generate the model"
             else id
  in wrap $
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
            Sat _ -> checkFormula1Model sym p q r =<< getModel proc

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
     r <- freshConstant sym (safeSymbol "r8") (BaseBVRepr (knownNat @8))
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
longTimeTest (SolverName nm, AnOnlineSolver (Proxy :: Proxy s), features, opts, mb'timeoutOpt) goal_tmo =
  TCL.withChecklist "timer tests" $
  withIONonceGenerator $ \gen ->
  do sym <- newExprBuilder FloatUninterpretedRepr State gen
     extendConfig opts (getConfiguration sym)

     -- Configure a solver timeout in What4 if specified for this test.
     case goal_tmo of
       Nothing -> return ()
       Just t -> case mb'timeoutOpt of
         Nothing -> error $ "No goal timeout option for backend solver " <> nm
         Just timeoutOpt -> do
           tmOpt <- getOptionSetting timeoutOpt $ getConfiguration sym
           warnings <- setOpt tmOpt $ floor (t # milli Second)
           TCL.check "timer option set" null warnings

     f <- mkFormula2 sym

     proc <- startSolverProcess @s features Nothing sym
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


main :: IO ()
main = do
  testLevel <- TestLevel . fromMaybe "0" <$> lookupEnv "CI_TEST_LEVEL"
  versionedSolvers <- zip allOnlineSolvers
                      <$> mapM (getSolverVersion . testSolverName) allOnlineSolvers
  solvers <- reportSolverVersions testLevel testSolverName versionedSolvers
  defaultMain $
    testGroup "OnlineSolverTests"
    [
      testGroup "SmokeTest" $ map mkSmokeTest solvers
    , testGroup "QuickStart Framed" $ map (quickstartTest True)  solvers
    , testGroup "QuickStart Direct" $ map (quickstartTest False) solvers
    , timeoutTests testLevel solvers
    ]

-- Test the effects of general timeouts on solver proofs
--
-- n.b. Approximate times obviously highly variant based on test
-- machine, etc.  As long as they run consistently longer than the
-- useable threshold the tests should perform as expected.

timeoutTests :: TestLevel -> [(SolverTestData, SolverVersion)] -> TestTree
timeoutTests testLevel solvers =
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
      -- Also, people get bored.  But in practice, this will likely be
      -- set to a number of seconds to allow complex solver solutions
      -- to be obtained.
      --
      -- What4 also includes a deadman timeout on solver activity: the
      -- testTimeout is passed to the solver for voluntary timeouts,
      -- but if the solver does not honor this time specification,
      -- what4 will terminated it via a longer deadman timeout (longer
      -- to avoid triggering it unless needed because it's more
      -- impactful due to killing the solver process itself).
      --
      -- This value should also be <= 60% of useableTimeThreshold to
      -- ensure that the solver runs for a siginificantly longer
      -- period than the test timeout will be set to.
      --
      -- This value can be adjusted by the developer as needed to
      -- reasonably validate timeout testing subject to the above
      -- considerations.
      testTimeout = 250 % milli Second

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
      useableTimeThreshold = testTimeout
                             |+| (500 % milli Second) -- What4 deadman timeout
                             |+| (650 % milli Second) -- plus some extra time
      -- useableTimeThreshold = 4 % Second :: Time

      -- This is empirical data from previous runs of the "Test itself
      -- is valid and completes" test case; this data is used to guide
      -- the current evaluation; times here will be compared to the
      -- 'useableTimeThreshold' to verify that tests can be accurately
      -- run.  This table may need to be updated periodically by the
      -- developer as solvers, What4 formulation, and machine speeds
      -- evolve.
      approxTestTimes :: [ (SolverName, Time) ]
      approxTestTimes = [ (SolverName "Z3",         2.27 % Second)    -- Z3 4.8.10.  Z3 is good at self timeout.
                        , (SolverName "CVC4",       7.5  % Second)    -- CVC4 1.8
                        , (SolverName "Yices",      2.9  % Second)    -- Yices 2.6.1
                        , (SolverName "Boolector",  7.2  % Second)    -- Boolector 3.2.1
                        , (SolverName "STP",        1.35 % Second)    -- STP 2.3.3
                        ]

      -- This is the acceptable delta variation in time between the
      -- times in the approxTestTimes above and the actual test times.
      -- If difference between the two exceeds this amount then it
      -- represents a significant variation that should be attended
      -- to; either the values in the approxTestTimes needs to be
      -- updated to account for evolved functionality or the test
      -- formulas should be updated to ensure that reasonable timeout
      -- testing can be performed (or there is a significant
      -- performance regression or unexpected improvement in What4).
      --
      -- Note that when this test executable is run locally solo, a
      -- delta value of ~ 0.5 Second is sufficient.  This test is
      -- disabled when run via CI (i.e. CI_TEST_LEVEL is not 0),
      -- because *all* test executables are run in parallel via `cabal
      -- test` on unpredictable VMs, so it's not possible to exert any
      -- timing constraints in that situation.
      --
      -- Increase this as needed: it doesn't really have a negative
      -- affect on the actual timing tests, but it does decrease
      -- sensitivity in test timing changes.

      acceptableTimeDelta = 55.0 -- percent variance allowed from expected

      --------------------------------------------------
      -- end of expected developer-adjustments above  --
      --------------------------------------------------

      mkTimeoutTests (sti,sv) =
        let historical = fromMaybe (0.0 % Second)
                         $ lookup (testSolverName sti) approxTestTimes
            snamestr (SolverName sname) = sname
        in testGroup (snamestr $ testSolverName sti)
           [
             testCase ("Test itself is valid and completes (" <> show historical <> ")") $ do
               -- Verify that the solver will run to completion for
               -- this test if there is no time limit, and also that
               -- the approxTestTimes historical time is reasonably
               -- close to the actual time taken for this test.
               start <- getTime Monotonic
               longTimeTest sti Nothing @? "valid test"
               finish <- getTime Monotonic
               let deltaT = (fromInteger $ toNanoSecs $ diffTimeSpec start finish) % nano Second :: Time
               if testLevel == TestLevel "0"
                 then assertBool
                      ("actual duration of " <> show deltaT
                       <> " is significantly different than expected"
                       <> " (will not cause CI failure)")
                      $ qApprox (historical |* (acceptableTimeDelta / 100.0)) deltaT historical
                 else return ()

           , let maybeRunTest =
                   let tooFast = unwords
                                 [ "solver runs test faster than reasonable"
                                 , "timing threshold; skipping"
                                 ]
                   in if useableTimeThreshold |<| historical
                      then id
                      else ignoreTestBecause tooFast
             in maybeRunTest $ testCase "Test runs past timeout" $ do
               start <- getTime Monotonic
               rslt <- race
                       (threadDelay (floor $ useableTimeThreshold # micro Second))
                       (longTimeTest sti Nothing)
               finish <- getTime Monotonic
               let deltaT = (fromInteger $ toNanoSecs $ diffTimeSpec start finish) % nano Second :: Time
               isLeft rslt @? "solver is to fast for valid timeout testing"
               assertBool
                 ("Solver check query not interruptible (" <>
                   show deltaT <> " > expected " <> show useableTimeThreshold <> ")")
                 $ qApprox (useableTimeThreshold |* (acceptableTimeDelta / 100.0))  deltaT useableTimeThreshold

           -- Verify that specifying a goal-timeout will stop once
           -- that timeout is reached (i.e. before the race timeout here).
           , let maybeRunTest =
                   case (testSolverName sti, sv) of
                     -- Z3 4.8.12 goal-timeouts don't consistently
                     -- work properly.  Occasionally it will abort but
                     -- it generally seems to continue running and
                     -- cannot be aborted by signals from the what4
                     -- parent process.
                     (SolverName "Z3", SolverVersion v)  | "4.8.12" `elem` words v->
                       expectFailBecause "goal timeouts feature not effective"
                     _ -> id
             in maybeRunTest $ testCase ("Test with goal timeout (" <> show testTimeout <> ")") $ do
               rslt <- race
                       (threadDelay (floor $ useableTimeThreshold # micro Second))
                       (longTimeTest sti (Just testTimeout))
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

     ] <> map mkTimeoutTests solvers

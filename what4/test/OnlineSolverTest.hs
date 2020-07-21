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

import Control.Lens (folded)
import Control.Monad ( forM, void )
import Data.Char ( toLower )
import Data.Proxy
import System.Exit ( ExitCode(..) )
import System.Process ( readProcessWithExitCode )

import Test.Tasty
import Test.Tasty.HUnit

import Data.Parameterized.Nonce

import What4.Config
import What4.Interface
import What4.Expr
import What4.ProblemFeatures
import What4.Solver
import What4.Protocol.Online
import What4.Protocol.SMTWriter
import qualified What4.Protocol.SMTLib2 as SMT2
import qualified What4.Solver.Yices as Yices

data State t = State

allOnlineSolvers :: [(String, AnOnlineSolver, ProblemFeatures, [ConfigDesc])]
allOnlineSolvers =
  [ ("Z3", AnOnlineSolver @(SMT2.Writer Z3) Proxy, z3Features, z3Options)
  , ("CVC4",  AnOnlineSolver @(SMT2.Writer CVC4) Proxy, cvc4Features, cvc4Options)
  , ("Yices", AnOnlineSolver @Yices.Connection Proxy, yicesDefaultFeatures, yicesOptions)
  , ("Boolector", AnOnlineSolver @(SMT2.Writer Boolector) Proxy, boolectorFeatures, boolectorOptions)
  , ("STP", AnOnlineSolver @(SMT2.Writer STP) Proxy, stpFeatures, stpOptions)
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

mkQuickstartTest :: (String, AnOnlineSolver, ProblemFeatures, [ConfigDesc]) -> TestTree
mkQuickstartTest (nm, AnOnlineSolver (Proxy :: Proxy s), features, opts) = testCase nm $
  withIONonceGenerator $ \gen ->
  do sym <- newExprBuilder FloatUninterpretedRepr State gen
     extendConfig opts (getConfiguration sym)

     proc <- startSolverProcess @s features Nothing sym
     let conn = solverConn proc

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

     (p',q',r') <- inNewFrame proc $
       do assume conn f
          res <- check proc "quickstart query 1"
          case res of
            Unsat _ -> fail "Unsatisfiable"
            Unknown -> fail "Solver returned UNKNOWN"
            Sat _ ->
              do eval <- getModel proc
                 p' <- groundEval eval p
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

     inNewFrame proc $
       do assume conn f
          assume conn block
          res <- check proc "quickstart query 2"
          case res of
            Unsat _ -> return ()
            Unknown -> fail "Solver returned UNKNOWN"
            Sat _   -> fail "Should be a unique model!"



mkQuickstartTestAlt :: (String, AnOnlineSolver, ProblemFeatures, [ConfigDesc]) -> TestTree
mkQuickstartTestAlt (nm, AnOnlineSolver (Proxy :: Proxy s), features, opts) = testCase nm $
  withIONonceGenerator $ \gen ->
  do sym <- newExprBuilder FloatUninterpretedRepr State gen
     extendConfig opts (getConfiguration sym)

     proc <- startSolverProcess @s features Nothing sym
     let conn = solverConn proc

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

     (p',q',r') <-
       do assume conn f
          res <- check proc "quickstart query 1"
          case res of
            Unsat _ -> fail "Unsatisfiable"
            Unknown -> fail "Solver returned UNKNOWN"
            Sat _ ->
              do eval <- getModel proc
                 p' <- groundEval eval p
                 q' <- groundEval eval q
                 r' <- groundEval eval r
                 return (p',q',r')

     reset proc

     -- This is the unique satisfiable model
     p' == False @? "p value"
     q' == False @? "q value"
     r' == True  @? "r value"

     -- Compute a blocking predicate for the computed model
     bs <- forM [(p,p'),(q,q'),(r,r')] $ \(x,v) -> eqPred sym x (backendPred sym v)
     block <- notPred sym =<< andAllOf sym folded bs

     assume conn f
     assume conn block
     res <- check proc "quickstart query 2"
     case res of
       Unsat _ -> return ()
       Unknown -> fail "Solver returned UNKNOWN"
       Sat _   -> fail "Should be a unique model!"


getSolverVersion :: String -> IO String
getSolverVersion solver = do
  (r,o,e) <- readProcessWithExitCode (toLower <$> solver) ["--version"] ""
  if r == ExitSuccess
    then let ol = lines o in
           return $ if null ol then (solver <> " v??") else head ol
    else return $ solver <> " version error: " <> show r <> " /;/ " <> e


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
    [ testGroup "SmokeTest" $ map mkSmokeTest allOnlineSolvers
    , testGroup "QuickStart" $ map mkQuickstartTest allOnlineSolvers
    , testGroup "QuickStart Alternate" $ map mkQuickstartTestAlt allOnlineSolvers
    ]

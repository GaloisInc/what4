{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import           Test.Tasty
import           Test.Tasty.HUnit

import Data.Foldable (forM_)
import Data.List (length)
import System.IO (FilePath, IOMode(..), openFile, hClose)
import System.IO.Temp (withSystemTempFile)
import Data.Text
import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some (Some(..))

import What4.Config (extendConfig)
import What4.Expr
         ( ExprBuilder,  FloatModeRepr(..), newExprBuilder
         , BoolExpr, IntegerExpr, GroundValue, groundEval
         , EmptyExprBuilderState(..))
import What4.Interface
         ( BaseTypeRepr(..), getConfiguration
         , freshConstant, safeSymbol, notPred
         , impliesPred, intLit, intAdd, intLe )
import What4.Solver
import What4.Symbol (SolverSymbol(..))
import What4.Protocol.SMTLib2 as SMT2
         (assume, sessionWriter, runCheckSat, runGetAbducts, Writer)
import What4.Protocol.SMTWriter
         (mkSMTTerm)
import What4.Protocol.Online

cvc5executable :: FilePath
cvc5executable = "cvc5"

-- Call the online getAbduct tactic
testGetAbductOnline ::
  ExprBuilder t st fs ->
  [BoolExpr t] ->
  BoolExpr t ->
  Int ->
  IO [String]
testGetAbductOnline sym hs g n = do
  -- Print SMT file in /tmp/
  withSystemTempFile "what4abdonline" $ \fname mirroredOutput -> do
    proc <- startSolverProcess @(SMT2.Writer CVC5) cvc5Features (Just mirroredOutput) sym
    let conn = solverConn proc
    inNewFrame proc $ do
      mapM_ (\x -> assume conn x) hs
      getAbducts proc n (pack "abd") g
    -- hClose mirroredOutput

-- Call the offline getAbduct tactic
testGetAbductOffline ::
  ExprBuilder t st fs ->
  BoolExpr t ->
  Int ->
  IO [String]
testGetAbductOffline sym f n = do
  -- Print SMT file in /tmp/
  withSystemTempFile "what4abdoffline" $ \fname mirroredOutput -> do
    let logData = LogData { logCallbackVerbose = \_ _ -> return ()
                           , logVerbosity = 2
                           , logReason = "defaultReason"
                           , logHandle = Just mirroredOutput }
    withCVC5 sym cvc5executable logData $ \session -> do
      f_term <- mkSMTTerm (sessionWriter session) f
      runGetAbducts session n (pack "abd") f_term
    --hClose mirroredOutput

-- Prove f using an SMT solver, by checking if ~f is unsatisfiable
prove ::
  ExprBuilder t st fs ->
  BoolExpr t ->
  [(String, IntegerExpr t)] ->
  IO (SatResult () ())
prove sym f es = do
  -- Print SMT file in /tmp/
  withSystemTempFile "what4prove" $ \fname mirroredOutput -> do
    proc <- startSolverProcess @(SMT2.Writer CVC5) cvc5Features (Just mirroredOutput) sym
    let logData = LogData { logCallbackVerbose = \_ _ -> return ()
                           , logVerbosity = 2
                           , logReason = "defaultReason"
                           , logHandle = Just mirroredOutput }
    
    -- To prove f, we check whether not f is unsat
    notf <- notPred sym f
    withCVC5 sym cvc5executable logData $ \session -> do
      checkSatisfiable proc "test" notf

-- Tests

testAbdOnline :: ExprBuilder t st fs -> 
  [BoolExpr t] -> 
  BoolExpr t -> 
  TestTree
testAbdOnline sym hs g = testCase "getting 3 abducts using cvc5 online" $ do
  -- Ask for 3 abducts for f
  res <- testGetAbductOnline sym hs g 3
  (Data.List.length res == 3) @? "3 online abducts"

testAbdOffline :: ExprBuilder t st fs -> 
  BoolExpr t -> 
  [(String, IntegerExpr t)] -> 
  TestTree
testAbdOffline sym f es = testCase "getting 3 abducts using cvc5 offline" $ do
  -- Ask for 3 abducts for f
  res <- testGetAbductOffline sym f 3
  (Data.List.length res == 3) @? "3 offline abducts"

testSatAbd :: ExprBuilder t st fs -> 
  BoolExpr t -> 
  [(String, IntegerExpr t)] -> 
  TestTree
testSatAbd sym f es = testCase "testing SAT query for abduction" $ do
  -- Prove f (is ~f unsatisfiable?). We expect ~f to be satisfiable
  res <- prove sym f es
  isSat res @? "sat"


main :: IO ()
main = do
  Some ng <- newIONonceGenerator
  sym <- newExprBuilder FloatIEEERepr EmptyExprBuilderState ng

  -- This line is necessary for working with cvc5.
  extendConfig cvc5Options (getConfiguration sym)

  -- Build this formula: ~(y >= 0 => (x + y + z) >= 0)
  
  -- First, declare fresh constants for each of the three variables x, y, z.
  x <- freshConstant sym (safeSymbol "x") BaseIntegerRepr
  y <- freshConstant sym (safeSymbol "y") BaseIntegerRepr
  z <- freshConstant sym (safeSymbol "z") BaseIntegerRepr

  -- Next, build up the clause
  zero <- intLit sym 0                    -- 0
  pxyz <- intAdd sym x =<< intAdd sym y z -- x + y + z
  ygte0 <- intLe sym zero y               -- 0 <= y
  xyzgte0 <- intLe sym zero pxyz          -- 0 <= (x + y + z) 
  f <- impliesPred sym ygte0 xyzgte0      -- (0 <= y) -> (0 <= (x + y + z))

  defaultMain $ testGroup "Tests" $
    [ -- test passes if f is disproved (~f is sat)
      testSatAbd sym f [ ("x", x)
                     , ("y", y)
                     , ("z", z)
                           ],
      -- test passes if cvc5 returns 3 abducts (offline)
      testAbdOffline sym f [ ("x", x)
                     , ("y", y)
                     , ("z", z)
                     ],
      -- test passes if cvc5 returns 3 abducts (online)
      testAbdOnline sym [ygte0] xyzgte0
    ]
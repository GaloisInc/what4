{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import           Test.Tasty
import           Test.Tasty.HUnit

import Data.Foldable (forM_)
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

testGetAbductOnline ::
  ExprBuilder t st fs ->
  [BoolExpr t] ->
  BoolExpr t ->
  IO ()
testGetAbductOnline sym hs g = do
  withSystemTempFile "what4abdonline" $ \fname mirroredOutput -> do
    proc <- startSolverProcess @(SMT2.Writer CVC5) cvc5Features (Just mirroredOutput) sym
    let conn = solverConn proc
    inNewFrame proc $ do
      mapM_ (\x -> assume conn x) hs
      res <- getAbducts proc 5 (pack "abd") g
      putStrLn ("Abducts:")
      forM_ res putStrLn
    hClose mirroredOutput

testGetAbductOffline ::
  ExprBuilder t st fs ->
  BoolExpr t ->
  Int ->
  IO ()
testGetAbductOffline sym f n = do
  -- Print SMT file in /tmp/
  withSystemTempFile "what4abdoffline" $ \fname mirroredOutput -> do
    let logData = LogData { logCallbackVerbose = \_ _ -> return ()
                           , logVerbosity = 2
                           , logReason = "defaultReason"
                           , logHandle = Just mirroredOutput }
    withCVC5 sym cvc5executable logData $ \session -> do
      f_term <- mkSMTTerm (sessionWriter session) f
      putStrLn "Abducts:"
      abd <- runGetAbducts session n (pack "abd") f_term 
      forM_ abd putStrLn
    hClose mirroredOutput

-- | Determine whether a predicate is satisfiable, and print out the values of a
-- set of expressions if a satisfying instance is found.
prove ::
  ExprBuilder t st fs ->
  BoolExpr t ->
  [(String, IntegerExpr t)] ->
  IO (SatResult () ())
prove sym f es = do
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

testSatAbd :: TestTree
testSatAbd = testCase "testing SAT query for abduction" $ do
  Some ng <- newIONonceGenerator
  sym <- newExprBuilder FloatIEEERepr EmptyExprBuilderState ng

  -- This line is necessary for working with cvc5.
  extendConfig cvc5Options (getConfiguration sym)

  -- The following is expected to be satisfiable. Let's check with cvc5
  --   not (y >= 0 => (x + y + z) >= 0)
  
  -- First, declare fresh constants for each of the three variables x, y, z.
  x <- freshConstant sym (safeSymbol "x") BaseIntegerRepr
  y <- freshConstant sym (safeSymbol "y") BaseIntegerRepr
  z <- freshConstant sym (safeSymbol "z") BaseIntegerRepr

  -- Next, build up the clause
  zero <- intLit sym 0                        -- 0
  pxyz <- intAdd sym x =<< intAdd sym y z -- x + y + z
  ygte0 <- intLe sym zero y               -- 0 <= y
  xyzgte0 <- intLe sym zero pxyz          -- 0 <= (x + y + z) 
  f <- impliesPred sym ygte0 xyzgte0      -- (0 <= y) -> (0 <= (x + y + z))

  -- Prove f (is ~f unsatisfiable?), and otherwise, print countermodel and a formula that will allow me to prove f
  putStrLn "Offline SMT calls"
  res <- prove sym f [ ("x", x)
                     , ("y", y)
                     , ("z", z)
                     ]
  isUnsat res @? "unsat"

main :: IO ()
main = do
  {-Some ng <- newIONonceGenerator
  sym <- newExprBuilder FloatIEEERepr EmptyExprBuilderState ng

  -- This line is necessary for working with cvc5.
  extendConfig cvc5Options (getConfiguration sym)

  -- The following is expected to be satisfiable. Let's check with cvc5
  --   not (y >= 0 => (x + y + z) >= 0)
  
  -- First, declare fresh constants for each of the three variables x, y, z.
  x <- freshConstant sym (safeSymbol "x") BaseIntegerRepr
  y <- freshConstant sym (safeSymbol "y") BaseIntegerRepr
  z <- freshConstant sym (safeSymbol "z") BaseIntegerRepr

  -- Next, build up the clause
  zero <- intLit sym 0                        -- 0
  pxyz <- intAdd sym x =<< intAdd sym y z -- x + y + z
  ygte0 <- intLe sym zero y               -- 0 <= y
  xyzgte0 <- intLe sym zero pxyz          -- 0 <= (x + y + z) 
  f <- impliesPred sym ygte0 xyzgte0      -- (0 <= y) -> (0 <= (x + y + z))

  -- Prove f (is ~f unsatisfiable?), and otherwise, print countermodel and a formula that will allow me to prove f
  putStrLn "Offline SMT calls"
  res <- prove sym f [ ("x", x)
                     , ("y", y)
                     , ("z", z)
                     ]
  if (isSat res) then do
    -- This query to the SMT solver: (get-abduct A (=> (>= y 0) (>= (+ x y z) 0)))
    putStrLn "\nOnline call to get-abduct"
    testGetAbductOnline sym [ygte0] xyzgte0
    putStrLn "\n\nOffline call to get-abduct"
    testGetAbductOffline sym f 5
  else if (isUnsat res) then
    putStrLn "\ncvc5 proved goal"
  else
    putStrLn "\ncvc5 returned Unknown!"-}
  defaultMain $ testGroup "Tests" $
    [ testSatAbd ]
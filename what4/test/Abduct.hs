{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
module Main where

import Data.Foldable (forM_)
import System.IO (FilePath, IOMode(..), openFile)

import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some (Some(..))

import What4.Config (extendConfig)
import What4.Expr
         ( ExprBuilder,  FloatModeRepr(..), newExprBuilder
         , BoolExpr, IntegerExpr, GroundValue, groundEval
         , EmptyExprBuilderState(..) )
import What4.Interface
         ( BaseTypeRepr(..), getConfiguration
         , freshConstant, safeSymbol, notPred
         , impliesPred, intLit, intAdd, intLe )
import What4.Solver
         (LogData(..), defaultLogData, cvc5Options, withCVC5, cvc5Options, withCVC5, SatResult(..))
import What4.Protocol.SMTLib2
         (assume, sessionWriter, runCheckSat, runGetAbduct)
import What4.Protocol.SMTWriter
         (mkSMTTerm)

cvc5executable :: FilePath
cvc5executable = "cvc5"

main :: IO ()
main = do
  Some ng <- newIONonceGenerator
  sym <- newExprBuilder FloatIEEERepr EmptyExprBuilderState ng

  -- This line is necessary for working with cvc5.
  extendConfig cvc5Options (getConfiguration sym)

  -- The following is satisfiable. Let's get an abduct from the SMT solver,
  -- Some formula that will make it unsatisfiable (its negation provable)
  -- not (y >= 0 => (x + y + z) >= 0)
  -- This query to the SMT solver: (get-abduct A (=> (>= y 0) (>= (+ x y z) 0)))
  
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
  prove sym f [ ("x", x)
              , ("y", y)
              , ("z", z)
              ]

testGetAbduct :: 
  ExprBuilder t st fs ->
  BoolExpr t ->
  [(String, IntegerExpr t)] ->
  Int ->
  IO ()
testGetAbduct sym f es n = do
  -- Print SMT file in /tmp/
  mirroredOutput <- openFile "/tmp/what4abduct.smt2" ReadWriteMode
  let logData = LogData { logCallbackVerbose = \_ _ -> return ()
                         , logVerbosity = 2
                         , logReason = "defaultReason"
                         , logHandle = Just mirroredOutput }
  withCVC5 sym cvc5executable logData $ \session -> do
    f_term <- mkSMTTerm (sessionWriter session) f
    abd <- runGetAbduct session "abd" f_term n
    forM_ abd putStrLn

-- | Determine whether a predicate is satisfiable, and print out the values of a
-- set of expressions if a satisfying instance is found.
prove ::
  ExprBuilder t st fs ->
  BoolExpr t ->
  [(String, IntegerExpr t)] ->
  IO ()
prove sym f es = do
  -- We will use cvc5 to determine if f is satisfiable.
  mirroredOutput <- openFile "/tmp/what4abductprove.smt2" ReadWriteMode
  let logData = LogData { logCallbackVerbose = \_ _ -> return ()
                         , logVerbosity = 2
                         , logReason = "defaultReason"
                         , logHandle = Just mirroredOutput }
  notf <- notPred sym f
  withCVC5 sym cvc5executable logData $ \session -> do
    -- Assume f is true.
    assume (sessionWriter session) notf
    runCheckSat session $
      \case
        Sat (ge, _) -> do
          putStrLn "Satisfiable, with model:"
          forM_ es $ \(nm, e) -> do
            v <- groundEval ge e
            putStrLn $ "  " ++ nm ++ " := " ++ show v
          putStrLn "\nEach of the following formulas would make the goal unsatisfiable:"
          testGetAbduct sym f es 5
        Unsat _ -> putStrLn "Unsatisfiable."
        Unknown -> putStrLn "Solver failed to find a solution."
    putStrLn ""
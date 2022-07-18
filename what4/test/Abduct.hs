{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Data.Foldable (forM_)
import System.IO (FilePath, IOMode(..), openFile, hClose)
import Data.Bimap (keys)
import Data.List (map)
import Data.Text (unpack)

import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some (Some(..))

import What4.Config (extendConfig)
import What4.Expr.Builder (SymbolVarBimap(SymbolVarBimap))
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
         (WriterConn(..), mkSMTTerm)
import What4.Protocol.Online

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
  putStrLn "Offline SMT calls"
  prove sym f [ ("x", x)
              , ("y", y)
              , ("z", z)
              ]

  putStrLn "\nOnline call to get abduct"
  putStrLn "Assert hypothesis, and get-abduct on goal"
  testGetAbductOnline sym [ygte0] xyzgte0


testGetAbducts ::
  ExprBuilder t st fs ->
  BoolExpr t ->
  Int ->
  IO ()
testGetAbducts sym f n = do
  -- Print SMT file in /tmp/
  mirroredOutput <- openFile "/tmp/what4abduct.smt2" ReadWriteMode
  let logData = LogData { logCallbackVerbose = \_ _ -> return ()
                         , logVerbosity = 2
                         , logReason = "defaultReason"
                         , logHandle = Just mirroredOutput }
  withCVC5 sym cvc5executable logData $ \session -> do
    f_term <- mkSMTTerm (sessionWriter session) f
    putStrLn "Abducts:"
    abd <- runGetAbducts session n "abd" f_term 
      [(Bool, [("=", [Intgr, Intgr]),
               (">=", [Intgr, Intgr]),
               ("and", [Bool, Bool])]), 
       (Intgr, [("x", []),
                ("y", []),
                ("z", []),
                ("0", []),
                ("+", [Intgr, Intgr]),
                ("-", [Intgr, Intgr])])]
    forM_ abd putStrLn
  hClose mirroredOutput

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
          testGetAbducts sym f 5
        Unsat _ -> putStrLn "Unsatisfiable."
        Unknown -> putStrLn "Solver failed to find a solution."
    putStrLn ""
  hClose mirroredOutput

testGetAbductOnline ::
  ExprBuilder t st fs ->
  [BoolExpr t] ->
  BoolExpr t ->
  IO ()
testGetAbductOnline sym hs g = do
  mirroredOutput <- openFile "/tmp/what4abductproveonline.smt2" ReadWriteMode
  proc <- startSolverProcess @(SMT2.Writer CVC5) cvc5Features (Just mirroredOutput) sym
  let conn = solverConn proc
  inNewFrame proc $ do
    mapM_ (\x -> assume conn x) hs
    res <- getAbducts proc 5 "abd" g
      [(Bool, [("=", [Intgr, Intgr]),
               ("and", [Bool, Bool]),
               (">=", [Intgr, Intgr])]), 
       (Intgr, [("x", []),
                ("y", []),
                ("z", []),
                ("0", []),
                ("+", [Intgr, Intgr]),
                ("-", [Intgr, Intgr])])]

  {- This code will be useful for automatically detecting variables within the getAbduct what4 function to put in the grammar:  
    putStrLn "In testGetAbductOnline, created SMT term, variables are:"
    -- session -> WriterConn -> SymbolVarBimap
    let vars = varBindings (solverConn proc)
    -- SymbolVarBimap -> Bimap -> List of pairs
    -- bimap <- Data.Bimap.assocs (SymbolVarBimap vars)
        bimap = case vars of SymbolVarBimap vars' -> vars'
        symbols = keys bimap
        symbolsStr = map (\x -> unpack (solverSymbolAsText x)) symbols
    forM_ symbolsStr putStrLn
  -}
    putStrLn ("Abducts:")
    forM_ res putStrLn
  hClose mirroredOutput
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module W4SMT2
  ( solve
  , solveFile
  , main
  ) where

import Data.Parameterized.Nonce qualified as Nonce
import Data.Text (Text)
import Data.Text.IO qualified as Text.IO
import System.Environment qualified as Env
import System.Exit qualified as Exit
import System.IO qualified as IO

import What4.Expr qualified as WE
import What4.FloatMode qualified as WFM
import What4.Interface qualified as WI
import What4.SatResult qualified as WSR

import W4SMT2.Exec qualified as Exec
import W4SMT2.Parser qualified as Parser

-- | Solve an SMT-Lib 2 problem provided as 'Text'.
solve ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO (), ?writeStdout :: Text -> IO ()) =>
  sym ->
  Text ->
  IO (WSR.SatResult () ())
solve sym input = do
  sexps <- Parser.parseSExps input
  Exec.execCommands sym Exec.initState sexps

-- | Solve an SMT-Lib 2 problem from a file.
solveFile ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO (), ?writeStdout :: Text -> IO ()) =>
  sym ->
  FilePath ->
  IO (WSR.SatResult () ())
solveFile sym path = do
  contents <- Text.IO.readFile path
  solve sym contents

main :: IO ()
main = do
  args <- Env.getArgs
  input <- case args of
    [] -> Text.IO.getContents
    [path] -> Text.IO.readFile path
    _ -> do
      IO.hPutStrLn IO.stderr "Usage: w4smt2 [FILE]"
      IO.hPutStrLn IO.stderr "  If FILE is not provided, reads from stdin."
      Exit.exitFailure
  result <- let ?logStderr = Text.IO.hPutStrLn IO.stderr
                ?writeStdout = Text.IO.putStrLn
            in Nonce.withIONonceGenerator $ \gen -> do
      sym <- WE.newExprBuilder WFM.FloatUninterpretedRepr WE.EmptyExprBuilderState gen
      solve sym input
  case result of
    WSR.Sat () -> putStrLn "sat"
    WSR.Unsat () -> putStrLn "unsat"
    WSR.Unknown -> putStrLn "unknown"

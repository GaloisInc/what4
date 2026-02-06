{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module W4SMT2.Solve
  ( solve
  , solveFile
  , solveWithSolver
  ) where

import Control.Monad qualified as Monad
import Data.Text (Text)
import Data.Text.IO qualified as Text.IO

import What4.Config qualified as WCfg
import What4.Expr qualified as WE
import What4.Interface qualified as WI
import What4.Protocol.SMTLib2 qualified as SMT2
import What4.SatResult qualified as WSR
import What4.Solver.Adapter (defaultLogData)
import What4.Solver.Bitwuzla qualified as Bitwuzla
import What4.Solver.CVC5 qualified as CVC5
import What4.Solver.Yices qualified as Yices
import What4.Solver.Z3 qualified as Z3

import W4SMT2.Exec qualified as Exec
import W4SMT2.Parser qualified as Parser

-- | Solver timeout in seconds.
solverTimeoutSeconds :: Integer
solverTimeoutSeconds = 300

-- | Solve an SMT-Lib 2 problem provided as 'Text'.
solve ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO (), ?writeStdout :: Text -> IO ()) =>
  sym ->
  Text ->
  IO (WSR.SatResult () ())
solve sym input = do
  sexps <- Parser.parseSExps input
  Exec.execCommands sym Exec.initState Nothing sexps

-- | Solve an SMT-Lib 2 problem from a file.
solveFile ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO (), ?writeStdout :: Text -> IO ()) =>
  sym ->
  FilePath ->
  IO (WSR.SatResult () ())
solveFile sym path = do
  contents <- Text.IO.readFile path
  solve sym contents

-- | Solve an SMT-Lib 2 problem with a specified external solver.
solveWithSolver ::
  (?logStderr :: Text -> IO (), ?writeStdout :: Text -> IO ()) =>
  String ->
  WE.ExprBuilder t st fs ->
  Text ->
  IO (Maybe (WSR.SatResult () ()))
solveWithSolver solverName sym input = do
  case makeSolverCallback solverName of
    Nothing -> return Nothing
    Just callback -> do
      sexps <- Parser.parseSExps input
      result <- Exec.execCommands sym Exec.initState (Just callback) sexps
      return (Just result)

-- | Create a solver callback based on the solver name.
makeSolverCallback ::
  String ->
  Maybe (WE.ExprBuilder t st fs -> [WI.Pred (WE.ExprBuilder t st fs)] -> IO (WSR.SatResult () ()))
makeSolverCallback = \case
  "z3" -> Just invokeZ3
  "yices" -> Just invokeYices
  "cvc5" -> Just invokeCVC5
  "bitwuzla" -> Just invokeBitwuzla
  _ -> Nothing

normalizeSatResult :: WSR.SatResult a b -> IO (WSR.SatResult () ())
normalizeSatResult = \case
  WSR.Sat _ -> return (WSR.Sat ())
  WSR.Unsat _ -> return (WSR.Unsat ())
  WSR.Unknown -> return WSR.Unknown

-- | Invoke Z3 with timeout configuration.
invokeZ3 ::
  WE.ExprBuilder t st fs ->
  [WI.Pred (WE.ExprBuilder t st fs)] ->
  IO (WSR.SatResult () ())
invokeZ3 sym preds = do
  let cfg = WI.getConfiguration sym
  WCfg.extendConfig Z3.z3Options cfg
  timeoutSetting <- WCfg.getOptionSetting Z3.z3Timeout cfg
  _ <- WCfg.setOpt timeoutSetting (solverTimeoutSeconds * 1000)
  Z3.withZ3 sym "z3" defaultLogData $ \session -> do
    let writer = SMT2.sessionWriter session
    Monad.forM_ preds $ SMT2.assume writer
    SMT2.runCheckSat session normalizeSatResult

-- | Invoke Yices with timeout configuration.
invokeYices ::
  WE.ExprBuilder t st fs ->
  [WI.Pred (WE.ExprBuilder t st fs)] ->
  IO (WSR.SatResult () ())
invokeYices sym preds = do
  let cfg = WI.getConfiguration sym
  WCfg.extendConfig Yices.yicesOptions cfg
  timeoutSetting <- WCfg.getOptionSetting Yices.yicesGoalTimeout cfg
  _ <- WCfg.setOpt timeoutSetting solverTimeoutSeconds
  Yices.runYicesInOverride sym defaultLogData preds normalizeSatResult

-- | Invoke CVC5 with timeout configuration.
invokeCVC5 ::
  WE.ExprBuilder t st fs ->
  [WI.Pred (WE.ExprBuilder t st fs)] ->
  IO (WSR.SatResult () ())
invokeCVC5 sym preds = do
  let cfg = WI.getConfiguration sym
  WCfg.extendConfig CVC5.cvc5Options cfg
  timeoutSetting <- WCfg.getOptionSetting CVC5.cvc5Timeout cfg
  _ <- WCfg.setOpt timeoutSetting (solverTimeoutSeconds * 1000)
  CVC5.withCVC5 sym "cvc5" defaultLogData $ \session -> do
    let writer = SMT2.sessionWriter session
    Monad.forM_ preds $ SMT2.assume writer
    SMT2.runCheckSat session normalizeSatResult

-- | Invoke Bitwuzla with timeout configuration.
invokeBitwuzla ::
  WE.ExprBuilder t st fs ->
  [WI.Pred (WE.ExprBuilder t st fs)] ->
  IO (WSR.SatResult () ())
invokeBitwuzla sym preds = do
  let cfg = WI.getConfiguration sym
  WCfg.extendConfig Bitwuzla.bitwuzlaOptions cfg
  timeoutSetting <- WCfg.getOptionSetting Bitwuzla.bitwuzlaTimeout cfg
  _ <- WCfg.setOpt timeoutSetting (solverTimeoutSeconds * 1000)
  Bitwuzla.withBitwuzla sym "bitwuzla" defaultLogData $ \session -> do
    let writer = SMT2.sessionWriter session
    Monad.forM_ preds $ SMT2.assume writer
    SMT2.runCheckSat session normalizeSatResult

------------------------------------------------------------------------
-- |
-- Module      : What4.Solver.ExternalABC
-- Description : Solver adapter code for an external ABC process via
--               SMT-LIB2.
-- Copyright   : (c) Galois, Inc 2020
-- License     : BSD3
-- Maintainer  : Aaron Tomb <atomb@galois.com>
-- Stability   : provisional
--
-- ABC-specific tweaks to the basic SMT-LIB2 solver interface.
------------------------------------------------------------------------
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

{-# LANGUAGE GADTs #-}
module What4.Solver.ExternalABC
  ( ExternalABC(..)
  , externalABCAdapter
  , abcPath
  , abcOptions
  , runExternalABCInOverride
  , writeABCSMT2File
  ) where

import           System.IO
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           What4.BaseTypes
import           What4.Concrete
import           What4.Config
import           What4.Expr.Builder
import           What4.Expr.GroundEval
import           What4.Interface
import           What4.ProblemFeatures
import qualified What4.Protocol.SMTLib2 as SMT2
import           What4.Protocol.SMTWriter
import           What4.SatResult
import           What4.Solver.Adapter
import           What4.Utils.Process

data ExternalABC = ExternalABC deriving Show

-- | Path to ABC
abcPath :: ConfigOption (BaseStringType Unicode)
abcPath = configOption knownRepr "abc_path"

abcOptions :: [ConfigDesc]
abcOptions =
  [ mkOpt
      abcPath
      executablePathOptSty
      (Just (PP.text "ABC executable path"))
      (Just (ConcreteString "abc"))
  ]

externalABCAdapter :: SolverAdapter st
externalABCAdapter =
  SolverAdapter
  { solver_adapter_name = "ABC"
  , solver_adapter_config_options = abcOptions
  , solver_adapter_check_sat = runExternalABCInOverride
  , solver_adapter_write_smt2 = writeABCSMT2File
  }

indexType :: [SMT2.Sort] -> SMT2.Sort
indexType [i] = i
indexType il = SMT2.smtlib2StructSort @ExternalABC il

indexCtor :: [SMT2.Term] -> SMT2.Term
indexCtor [i] = i
indexCtor il = SMT2.smtlib2StructCtor @ExternalABC il

instance SMT2.SMTLib2Tweaks ExternalABC where
  smtlib2tweaks = ExternalABC

  smtlib2arrayType il r = SMT2.arraySort (indexType il) r

  smtlib2arrayConstant = Just $ \idx rtp v ->
    SMT2.arrayConst (indexType idx) rtp v
  smtlib2arraySelect a i = SMT2.arraySelect a (indexCtor i)
  smtlib2arrayUpdate a i = SMT2.arrayStore a (indexCtor i)

  smtlib2declareStructCmd _ = Nothing

abcFeatures :: ProblemFeatures
abcFeatures = useBitvectors

writeABCSMT2File
   :: ExprBuilder t st fs
   -> Handle
   -> [BoolExpr t]
   -> IO ()
writeABCSMT2File = SMT2.writeDefaultSMT2 ExternalABC "ABC" abcFeatures

instance SMT2.SMTLib2GenericSolver ExternalABC where
  defaultSolverPath _ = findSolverPath abcPath . getConfiguration

  defaultSolverArgs _ _ = do
    return ["-S", "%blast; &sweep -C 5000; &syn4; &cec -s -m -C 2000"]

  defaultFeatures _ = abcFeatures

  setDefaultLogicAndOptions _ = return ()

runExternalABCInOverride
  :: ExprBuilder t st fs
  -> LogData
  -> [BoolExpr t]
  -> (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) () -> IO a)
  -> IO a
runExternalABCInOverride =
  SMT2.runSolverInOverride ExternalABC nullAcknowledgementAction abcFeatures

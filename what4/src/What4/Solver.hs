{-|
Module      : What4.Solver
Description : Reexports for working with solvers
Copyright   : (c) Galois, Inc 2015-2020
License     : BSD3
Maintainer  : Rob Dockins <rdockins@galois.com>

The module reexports the most commonly used types
and operations for interacting with solvers.
-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}

module What4.Solver
  ( -- * Solver Adapters
    SolverAdapter(..)
  , ExprRangeBindings
  , defaultSolverAdapter
  , solverAdapterOptions
  , LogData(..)
  , logCallback
  , defaultLogData
  , smokeTest
  , module What4.SatResult

    -- * ABC (external, via SMT-Lib2)
  , ExternalABC(..)
  , externalABCAdapter
  , abcPath
  , abcOptions
  , runExternalABCInOverride
  , writeABCSMT2File

    -- * Boolector
  , Boolector(..)
  , boolectorAdapter
  , boolectorPath
  , runBoolectorInOverride
  , withBoolector
  , boolectorOptions
  , boolectorFeatures

    -- * CVC4
  , CVC4(..)
  , cvc4Adapter
  , cvc4Path
  , runCVC4InOverride
  , writeCVC4SMT2File
  , withCVC4
  , cvc4Options
  , cvc4Timeout
  , cvc4Features

    -- * DReal
  , DReal(..)
  , DRealBindings
  , drealAdapter
  , drealPath
  , runDRealInOverride
  , writeDRealSMT2File

    -- * STP
  , STP(..)
  , stpAdapter
  , stpPath
  , runSTPInOverride
  , withSTP
  , stpOptions
  , stpFeatures

    -- * Yices
  , yicesAdapter
  , yicesPath
  , runYicesInOverride
  , writeYicesFile
  , yicesOptions
  , yicesGoalTimeout
  , yicesDefaultFeatures

    -- * Z3
  , Z3(..)
  , z3Path
  , z3Adapter
  , runZ3InOverride
  , withZ3
  , z3Options
  , z3Timeout
  , z3Features
  ) where

import           What4.Solver.Adapter
import           What4.Solver.Boolector
import           What4.Solver.CVC4
import           What4.Solver.DReal
import           What4.Solver.ExternalABC
import           What4.Solver.STP
import           What4.Solver.Yices
import           What4.Solver.Z3
import           What4.SatResult

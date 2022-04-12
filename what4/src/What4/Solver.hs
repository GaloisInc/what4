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
  , boolectorTimeout
  , runBoolectorInOverride
  , withBoolector
  , boolectorOptions
  , boolectorFeatures

    -- * CVC4
  , CVC4(..)
  , cvc4Adapter
  , cvc4Path
  , cvc4Timeout
  , runCVC4InOverride
  , writeCVC4SMT2File
  , withCVC4
  , cvc4Options
  , cvc4Features

    -- * CVC5
  , CVC5(..)
  , cvc5Adapter
  , cvc5Path
  , cvc5Timeout
  , runCVC5InOverride
  , writeCVC5SMT2File
  , withCVC5
  , cvc5Options
  , cvc5Features

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
  , stpTimeout
  , runSTPInOverride
  , withSTP
  , stpOptions
  , stpFeatures

    -- * Yices
  , yicesAdapter
  , yicesPath
  , yicesEnableMCSat
  , yicesEnableInteractive
  , yicesGoalTimeout
  , runYicesInOverride
  , writeYicesFile
  , yicesOptions
  , yicesDefaultFeatures

    -- * Z3
  , Z3(..)
  , z3Path
  , z3Timeout
  , z3Tactic
  , z3TacticDefault
  , z3Adapter
  , runZ3InOverride
  , withZ3
  , z3Options
  , z3Features
  ) where

import           What4.Solver.Adapter
import           What4.Solver.Boolector
import           What4.Solver.CVC4
import           What4.Solver.CVC5
import           What4.Solver.DReal
import           What4.Solver.ExternalABC
import           What4.Solver.STP
import           What4.Solver.Yices
import           What4.Solver.Z3
import           What4.SatResult

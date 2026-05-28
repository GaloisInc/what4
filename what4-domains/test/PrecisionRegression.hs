{-
Module      : PrecisionRegression
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Exhaustive precision regression for Strides and StridedInterval operations at
width 4. See "PrecisionRegression.Common" for the methodology.

Per-domain results live in "PrecisionRegression.Strides" and
"PrecisionRegression.StridedInterval"; this module just dispatches to each
in turn. Setting @WHAT4_UPDATE_TEST_EXPECTATIONS=1@ refreshes both CSVs.
-}

module Main (main) where

import           System.Environment (lookupEnv)
import           System.Exit (exitFailure, exitSuccess)

import qualified PrecisionRegression.Strides as StridesReg
import           PrecisionRegression.Common (runDomain)
import qualified PrecisionRegression.StridedInterval as SIReg

main :: IO ()
main = do
  update <- (== Just "1") <$> lookupEnv "WHAT4_UPDATE_TEST_EXPECTATIONS"
  okStrides <- runDomain update StridesReg.csvPath StridesReg.results
  okSi <- runDomain update SIReg.csvPath SIReg.results
  if okStrides && okSi then exitSuccess else exitFailure

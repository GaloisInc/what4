{-
Module      : PrecisionRegression
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Exhaustive precision regression for the Arith and Bitwise domains at
width 4. See "PrecisionRegression.Common" for the methodology.

Per-domain results live in "PrecisionRegression.Arith" and
"PrecisionRegression.Bitwise"; this module just dispatches to each in
turn. Setting @WHAT4_UPDATE_TEST_EXPECTATIONS=1@ refreshes both CSVs.
-}

module Main (main) where

import           System.Environment (lookupEnv)

import           Test.Tasty (defaultMain, testGroup)

import           PrecisionRegression.Common (domainTests)
import qualified PrecisionRegression.Arith as ArithReg
import qualified PrecisionRegression.Bitwise as BitwiseReg

main :: IO ()
main = do
  update <- (== Just "1") <$> lookupEnv "WHAT4_UPDATE_TEST_EXPECTATIONS"
  arithTree   <- domainTests update "Arith"   ArithReg.csvPath   ArithReg.results
  bitwiseTree <- domainTests update "Bitwise" BitwiseReg.csvPath BitwiseReg.results
  defaultMain $ testGroup "precision_regression" [arithTree, bitwiseTree]

{-
Module      : PrecisionRegression.Strides
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Per-op precision results for the strides domain at width 4. The CSV is at
@test\/PrecisionRegression\/strides.csv@.
-}

{-# LANGUAGE DataKinds #-}

module PrecisionRegression.Strides
  ( stridesEnum
  , results
  , csvPath
  ) where

import qualified What4.Domains.BV.Strides as S

import           PrecisionRegression.Common

stridesEnum :: DomainEnum (S.Domain 4)
stridesEnum = DomainEnum (dedup S.toList enumStrides4) S.toList

results :: [Result]
results =
  [ leqResult stridesEnum "leq" S.leq
  , leqResult stridesEnum "leqPrecise" S.leqPrecise
  , leqResult stridesEnum "leqExact" S.leqExact
  , unaryResult stridesEnum "negate" (S.negate w4) cNegate
  , binaryResult stridesEnum "add" (S.add w4) cAdd
  , binaryResult stridesEnum "sub" (S.sub w4) cSub
  , scaleResult stridesEnum (\k -> S.scale w4 k)
  , binaryResult stridesEnum "mul" (S.mul w4) cMul
  , binaryResultFiltered stridesEnum "udiv" (S.udiv w4) cUdivPartial
  , binaryResultFiltered stridesEnum "urem" (S.urem w4) cUremPartial
  , binaryResultFiltered stridesEnum "sdiv" (S.sdiv w4) cSdivPartial
  , binaryResultFiltered stridesEnum "srem" (S.srem w4) cSremPartial
  , binaryResult stridesEnum "udivSmtlib" (S.udivSmtlib w4) cUdivSmtlib
  , binaryResult stridesEnum "uremSmtlib" (S.uremSmtlib w4) cUremSmtlib
  , binaryResult stridesEnum "sdivSmtlib" (S.sdivSmtlib w4) cSdivSmtlib
  , binaryResult stridesEnum "sremSmtlib" (S.sremSmtlib w4) cSremSmtlib
  , unaryResult stridesEnum "not" (S.not w4) cNot
  , binaryResult stridesEnum "and" (S.and w4) cAnd
  , binaryResult stridesEnum "or"  (S.or  w4) cOr
  , binaryResult stridesEnum "xor" (S.xor w4) cXor
  , binaryResult stridesEnum "shl"  (S.shl  w4) cShl
  , binaryResult stridesEnum "lshr" (S.lshr w4) cLshr
  , binaryResult stridesEnum "ashr" (S.ashr w4) cAshr
  , binaryResult stridesEnum "rol"  (S.rol  w4) cRol
  , binaryResult stridesEnum "ror"  (S.ror  w4) cRor
  ]

csvPath :: FilePath
csvPath = "test/PrecisionRegression/strides.csv"

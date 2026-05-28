{-
Module      : PrecisionRegression.CLP
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Per-op precision results for the CLP domain at width 4. The CSV is at
@test\/PrecisionRegression\/clp.csv@.
-}

{-# LANGUAGE DataKinds #-}

module PrecisionRegression.CLP
  ( clpEnum
  , results
  , csvPath
  ) where

import qualified What4.Domains.BV.CLP as C

import           PrecisionRegression.Common

clpEnum :: DomainEnum (C.Clp 4)
clpEnum = DomainEnum (dedup C.toList enumClps4) C.toList

results :: [Result]
results =
  [ unaryResult clpEnum "negate" (C.negate w4) cNegate
  , binaryResult clpEnum "add" (C.add w4) cAdd
  , binaryResult clpEnum "sub" (C.sub w4) cSub
  , scaleResult clpEnum (\k -> C.scale w4 k)
  , binaryResult clpEnum "mul" (C.mul w4) cMul
  , binaryResultFiltered clpEnum "udiv" (C.udiv w4) cUdivPartial
  , binaryResultFiltered clpEnum "urem" (C.urem w4) cUremPartial
  , binaryResultFiltered clpEnum "sdiv" (C.sdiv w4) cSdivPartial
  , binaryResultFiltered clpEnum "srem" (C.srem w4) cSremPartial
  , binaryResult clpEnum "udivSmtlib" (C.udivSmtlib w4) cUdivSmtlib
  , binaryResult clpEnum "uremSmtlib" (C.uremSmtlib w4) cUremSmtlib
  , binaryResult clpEnum "sdivSmtlib" (C.sdivSmtlib w4) cSdivSmtlib
  , binaryResult clpEnum "sremSmtlib" (C.sremSmtlib w4) cSremSmtlib
  , unaryResult clpEnum "not" (C.not w4) cNot
  , binaryResult clpEnum "and" (C.and w4) cAnd
  , binaryResult clpEnum "or"  (C.or  w4) cOr
  , binaryResult clpEnum "xor" (C.xor w4) cXor
  , binaryResult clpEnum "shl"  (C.shl  w4) cShl
  , binaryResult clpEnum "lshr" (C.lshr w4) cLshr
  , binaryResult clpEnum "ashr" (C.ashr w4) cAshr
  , binaryResult clpEnum "rol"  (C.rol  w4) cRol
  , binaryResult clpEnum "ror"  (C.ror  w4) cRor
  ]

csvPath :: FilePath
csvPath = "test/PrecisionRegression/clp.csv"

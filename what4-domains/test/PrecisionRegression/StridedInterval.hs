{-
Module      : PrecisionRegression.StridedInterval
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Per-op precision results for the StridedInterval domain at width 4. The CSV
is at @test\/PrecisionRegression\/si.csv@.
-}

{-# LANGUAGE DataKinds #-}

module PrecisionRegression.StridedInterval
  ( siEnum
  , results
  , csvPath
  ) where

import qualified What4.Domains.BV.StridedInterval as S

import           PrecisionRegression.Common

-- | Every proper 'S.Domain' at width 4: 'S.bottom' plus each enumerated
-- progression.
enumSi4 :: [S.Domain 4]
enumSi4 = S.bottom w4 : map S.mk enumStrides4

siEnum :: DomainEnum (S.Domain 4)
siEnum = DomainEnum (dedup S.toList enumSi4) S.toList

results :: [Result]
results =
  [ unaryResult siEnum "negate" (S.negate w4) cNegate
  , binaryResult siEnum "add" (S.add w4) cAdd
  , binaryResult siEnum "sub" (S.sub w4) cSub
  , scaleResult siEnum (\k -> S.scale w4 k)
  , binaryResult siEnum "mul" (S.mul w4) cMul
  , binaryResultFiltered siEnum "udiv" (S.udiv w4) cUdivPartial
  , binaryResultFiltered siEnum "urem" (S.urem w4) cUremPartial
  , binaryResultFiltered siEnum "sdiv" (S.sdiv w4) cSdivPartial
  , binaryResultFiltered siEnum "srem" (S.srem w4) cSremPartial
  , binaryResult siEnum "udivSmtlib" (S.udivSmtlib w4) cUdivSmtlib
  , binaryResult siEnum "uremSmtlib" (S.uremSmtlib w4) cUremSmtlib
  , binaryResult siEnum "sdivSmtlib" (S.sdivSmtlib w4) cSdivSmtlib
  , binaryResult siEnum "sremSmtlib" (S.sremSmtlib w4) cSremSmtlib
  , unaryResult siEnum "not" (S.not w4) cNot
  , binaryResult siEnum "and" (S.and w4) cAnd
  , binaryResult siEnum "or"  (S.or  w4) cOr
  , binaryResult siEnum "xor" (S.xor w4) cXor
  , binaryResult siEnum "shl"  (S.shl  w4) cShl
  , binaryResult siEnum "lshr" (S.lshr w4) cLshr
  , binaryResult siEnum "ashr" (S.ashr w4) cAshr
  , binaryResult siEnum "rol"  (S.rol  w4) cRol
  , binaryResult siEnum "ror"  (S.ror  w4) cRor
  , latticeResult siEnum "join" (S.join w4) cJoin
  , latticeResult siEnum "meet" (S.meet w4) cMeet
  ]

csvPath :: FilePath
csvPath = "test/PrecisionRegression/si.csv"

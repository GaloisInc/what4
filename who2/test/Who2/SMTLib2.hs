{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Who2.SMTLib2 (tests, goldenTests, discoverZ3ValidationTests) where

import Data.List (sort)
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString.Lazy as BSL
import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.NatRepr (knownNat)
import Data.Parameterized.Some (Some(Some))
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.Text.Lazy as Text.Lazy
import qualified Data.Text.Lazy.Builder as Builder
import System.Directory (listDirectory)
import System.Exit (ExitCode(ExitSuccess, ExitFailure))
import System.FilePath ((</>), (<.>), takeExtension, dropExtension)
import System.Process (readProcessWithExitCode)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (testCase, assertBool)

import qualified What4.Interface as WI
import qualified What4.Protocol.SMTLib2.Syntax as SMT2

import qualified Who2.TestBuilder as TB
import qualified Who2.Protocol.SMTLib2 as SMTWho2

-- | Main test entry point
tests :: IO TestTree
tests = do
  z3Tests <- discoverZ3ValidationTests "test-data/smt2"
  return $ testGroup "SMTLib2"
    [ goldenTests
    , testGroup "Z3 Validation" z3Tests
    ]

-- | Golden tests comparing generated SMT-Lib2 to expected output
goldenTests :: TestTree
goldenTests = testGroup "Golden Tests"
  [ -- Boolean operations
    goldenTest "truePred" $ \sym -> return $ WI.truePred sym
  , goldenTest "falsePred" $ \sym -> return $ WI.falsePred sym
  , goldenTest "notPred" $ \sym ->
      WI.notPred sym (WI.truePred sym)
  , goldenTest "andPred" $ \sym ->
      WI.andPred sym (WI.truePred sym) (WI.falsePred sym)
  , goldenTest "orPred" $ \sym ->
      WI.orPred sym (WI.truePred sym) (WI.falsePred sym)
  , goldenTest "xorPred" $ \sym ->
      WI.xorPred sym (WI.truePred sym) (WI.falsePred sym)
  , goldenTest "eqPred" $ \sym ->
      WI.eqPred sym (WI.truePred sym) (WI.falsePred sym)
  , goldenTest "itePred" $ \sym ->
      WI.itePred sym (WI.truePred sym) (WI.truePred sym) (WI.falsePred sym)

    -- Bitvector literals
  , goldenTest "bvLit-8" $ \sym ->
      WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 0x2A)
  , goldenTest "bvLit-16" $ \sym ->
      WI.bvLit sym (knownNat @16) (BV.mkBV knownNat 0x1234)
  , goldenTest "bvLit-32" $ \sym ->
      WI.bvLit sym (knownNat @32) (BV.mkBV knownNat 0xDEADBEEF)

    -- Arithmetic operations
  , goldenTest "bvAdd" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 10)
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 20)
      WI.bvAdd sym x y
  , goldenTest "bvSub" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 30)
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 10)
      WI.bvSub sym x y
  , goldenTest "bvMul" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 5)
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 7)
      WI.bvMul sym x y
  , goldenTest "bvNeg" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 42)
      WI.bvNeg sym x

    -- Bitwise operations
  , goldenTest "bvAndBits" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 0xFF)
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 0x0F)
      WI.bvAndBits sym x y
  , goldenTest "bvOrBits" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 0xF0)
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 0x0F)
      WI.bvOrBits sym x y
  , goldenTest "bvXorBits" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 0xFF)
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 0xAA)
      WI.bvXorBits sym x y
  , goldenTest "bvNotBits" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 0xAA)
      WI.bvNotBits sym x

    -- Shift operations
  , goldenTest "bvShl" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 0x0F)
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 2)
      WI.bvShl sym x y
  , goldenTest "bvLshr" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 0xF0)
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 2)
      WI.bvLshr sym x y
  , goldenTest "bvAshr" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 0xF0)
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 2)
      WI.bvAshr sym x y

    -- Division and remainder operations
  , goldenTest "bvUdiv" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 20)
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 4)
      WI.bvUdiv sym x y
  , goldenTest "bvUrem" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 23)
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 5)
      WI.bvUrem sym x y
  , goldenTest "bvSdiv" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 20)
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 4)
      WI.bvSdiv sym x y
  , goldenTest "bvSrem" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 23)
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 5)
      WI.bvSrem sym x y

    -- Rotation operations
  , goldenTest "bvRol" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 0x0F)
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 2)
      WI.bvRol sym x y
  , goldenTest "bvRor" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 0xF0)
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 2)
      WI.bvRor sym x y

    -- Bit manipulation operations
  , goldenTest "bvConcat" $ \sym -> do
      x <- WI.bvLit sym (knownNat @4) (BV.mkBV knownNat 0xA)
      y <- WI.bvLit sym (knownNat @4) (BV.mkBV knownNat 0x5)
      WI.bvConcat sym x y
  , goldenTest "bvSelect" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 0xFF)
      WI.bvSelect sym (knownNat @2) (knownNat @4) x
  , goldenTest "bvZext" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 0xFF)
      WI.bvZext sym (knownNat @16) x
  , goldenTest "bvSext" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 0xFF)
      WI.bvSext sym (knownNat @16) x

    -- Comparison operations
  , goldenTest "bvUlt" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 10)
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 20)
      WI.bvUlt sym x y
  , goldenTest "bvUle" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 10)
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 20)
      WI.bvUle sym x y
  , goldenTest "bvSlt" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat (-10))
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 20)
      WI.bvSlt sym x y
  , goldenTest "bvSle" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat (-10))
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 20)
      WI.bvSle sym x y
  , goldenTest "bvEq" $ \sym -> do
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 42)
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 42)
      WI.bvEq sym x y

    -- Bitvector ITE
  , goldenTest "bvIte" $ \sym -> do
      t <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 0xFF)
      f <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 0x00)
      WI.bvIte sym (WI.truePred sym) t f
  ]

-- | Discover Z3 validation tests from golden files directory
discoverZ3ValidationTests :: FilePath -> IO [TestTree]
discoverZ3ValidationTests dir = do
  files <- listDirectory dir
  let smt2Files = sort $ filter (\f -> takeExtension f == ".smt2") files
  return $ map (mkZ3Test dir) smt2Files
  where
    mkZ3Test :: FilePath -> FilePath -> TestTree
    mkZ3Test directory file =
      let name = dropExtension file
          goldenFile = directory </> file
      in testCase name $ do
        (exitCode, _, stderr) <- readProcessWithExitCode "z3" [goldenFile] ""
        case exitCode of
          ExitSuccess -> return ()
          ExitFailure code -> assertBool
            ("Z3 failed with exit code " ++ show code ++ "\nstderr: " ++ stderr)
            False

-- | Helper: create a golden test for a given operation
goldenTest :: String -> (forall t. TB.TestBuilder t -> IO (WI.SymExpr (TB.TestBuilder t) tp)) -> TestTree
goldenTest name mkExpr = goldenVsString name goldenFile $ do
  Some gen <- newIONonceGenerator
  sym <- TB.newTestBuilder gen
  expr <- mkExpr sym
  term <- SMTWho2.mkSMTTerm expr
  let output = renderSMT2WithHeader term
  return $ BSL.fromStrict $ Text.encodeUtf8 output
  where
    goldenFile = "test-data" </> "smt2" </> name <.> "smt2"

-- | Render a Term as SMT-Lib2 with proper header
renderSMT2WithHeader :: SMT2.Term -> Text.Text
renderSMT2WithHeader term =
  let header = "(set-logic QF_BV)\n"
      -- Wrap term in a tautology (= term term) for Z3 validation
      assertion = Text.Lazy.toStrict $ Builder.toLazyText $ SMT2.renderTerm (SMT2.eq [term, term])
      checkSat = "(check-sat)\n"
  in Text.concat [header, "(assert ", assertion, ")\n", checkSat]

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Control.Exception (try, SomeException)
import Data.IORef (newIORef, modifyIORef', readIORef)
import Data.Parameterized.Nonce (withIONonceGenerator)
import Data.Text.IO qualified as TIO
import Data.Text.Lazy qualified as TL
import Data.Text.Lazy.Encoding qualified as TLE
import System.Directory (listDirectory)
import System.FilePath ((</>), takeExtension, dropExtension, takeBaseName)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (testCase, (@?=))
import What4.Expr (newExprBuilder, EmptyExprBuilderState(EmptyExprBuilderState))
import What4.FloatMode (FloatModeRepr(FloatUninterpretedRepr))
import What4.SatResult (SatResult(Sat, Unsat, Unknown))

import W4SMT2 (solve)
import Z3Verification (mkZ3VerificationTests)

main :: IO ()
main = do
  goldenTests <- discoverTests "test/golden" mkSolverTest
  uxTests <- discoverTests "test/ux" mkUxTest
  qfBvTests <- discoverTests "test/qf-bv" mkSolverTest
  z3Tests <- mkZ3VerificationTests
  defaultMain $
    testGroup "w4smt2" $
    [ testGroup "golden" goldenTests
    , testGroup "ux" uxTests
    , testGroup "qf-bv" qfBvTests
    , testGroup "z3-verification" z3Tests
    ]

discoverTests :: FilePath -> (FilePath -> FilePath -> IO TestTree) -> IO [TestTree]
discoverTests dir mkTest = do
  files <- listDirectory dir
  let smt2Files = filter (\f -> takeExtension f == ".smt2") files
  mapM (mkTest dir) smt2Files

mkSolverTest :: FilePath -> FilePath -> IO TestTree
mkSolverTest dir file = do
  let name = dropExtension file
      inputPath = dir </> file
      goldenPath = dir </> name ++ ".out"
  return $ goldenVsString name goldenPath $ withIONonceGenerator $ \gen -> do
    let ?logStderr = \_ -> return ()
        ?writeStdout = \_ -> return ()
    sym <- newExprBuilder FloatUninterpretedRepr EmptyExprBuilderState gen
    input <- TIO.readFile inputPath
    result <- solve sym input
    let output = case result of
          Sat _ -> "sat\n"
          Unsat _ -> "unsat\n"
          Unknown -> "unknown\n"
    return (TLE.encodeUtf8 (TL.pack output))

mkUxTest :: FilePath -> FilePath -> IO TestTree
mkUxTest dir file = do
  let name = dropExtension file
      inputPath = dir </> file
      goldenPath = dir </> name ++ ".out"
  return $ testCase (takeBaseName inputPath) $ do
    input <- TIO.readFile inputPath
    stderrRef <- newIORef ""
    let ?logStderr = \t -> modifyIORef' stderrRef (<> t <> "\n")
        ?writeStdout = \_ -> return ()
    _ <- try @SomeException $ withIONonceGenerator $ \gen -> do
      sym <- newExprBuilder FloatUninterpretedRepr EmptyExprBuilderState gen
      solve sym input
    actualStderr <- readIORef stderrRef
    goldenStderr <- TIO.readFile goldenPath
    actualStderr @?= goldenStderr

{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}

module Z3Verification (mkZ3VerificationTests) where

import Control.Exception (try, SomeException)
import Data.Parameterized.Nonce (withIONonceGenerator)
import Data.Text.IO qualified as TIO
import System.Directory (listDirectory)
import System.Exit (ExitCode(ExitSuccess))
import System.FilePath ((</>), takeExtension, dropExtension)
import System.Process qualified as Process
import Test.Tasty (TestTree)
import Test.Tasty.HUnit (testCase, assertBool)
import What4.Expr (newExprBuilder, EmptyExprBuilderState(EmptyExprBuilderState))
import What4.FloatMode (FloatModeRepr(FloatUninterpretedRepr))
import What4.SatResult (SatResult(Sat, Unsat, Unknown))

import W4SMT2 (solve)

mkZ3VerificationTests :: IO [TestTree]
mkZ3VerificationTests = do
  z3Available <- checkZ3Available
  if not z3Available
    then return [testCase "Z3 not available - skipping" (assertBool "Z3 not found in PATH" True)]
    else do
      goldenTests <- collectTestFiles "test/golden"
      qfBvTests <- collectTestFiles "test/qf-bv"
      let allTests = goldenTests ++ qfBvTests
      mapM mkSingleZ3Test allTests

checkZ3Available :: IO Bool
checkZ3Available = do
  result <- try (Process.readProcessWithExitCode "z3" ["--version"] "") :: IO (Either SomeException (ExitCode, String, String))
  case result of
    Left _ -> return False
    Right (ExitSuccess, _, _) -> return True
    Right _ -> return False

collectTestFiles :: FilePath -> IO [(FilePath, FilePath)]
collectTestFiles dir = do
  files <- listDirectory dir
  let smt2Files = filter (\f -> takeExtension f == ".smt2") files
  return [(dir, f) | f <- smt2Files]

mkSingleZ3Test :: (FilePath, FilePath) -> IO TestTree
mkSingleZ3Test (dir, file) = do
  let name = dropExtension file
      inputPath = dir </> file
  return $ testCase name $ do
    w4Result <- let ?logStderr = \_ -> return ()
                    ?writeStdout = \_ -> return ()
                in withIONonceGenerator $ \gen -> do
      sym <- newExprBuilder FloatUninterpretedRepr EmptyExprBuilderState gen
      input <- TIO.readFile inputPath
      solve sym input

    z3Result <- runZ3OnFile inputPath

    case (w4Result, z3Result) of
      (Unknown, _) ->
        assertBool "w4smt2 returned Unknown (acceptable for incomplete solver)" True
      (Sat _, Sat _) ->
        assertBool "Results match: both SAT" True
      (Unsat _, Unsat _) ->
        assertBool "Results match: both UNSAT" True
      (Sat _, Unsat _) ->
        assertBool "MISMATCH: w4smt2=SAT but Z3=UNSAT" False
      (Unsat _, Sat _) ->
        assertBool "MISMATCH: w4smt2=UNSAT but Z3=SAT" False
      _ ->
        assertBool "Unexpected result combination" False

runZ3OnFile :: FilePath -> IO (SatResult () ())
runZ3OnFile filePath = do
  result <- try (Process.readProcessWithExitCode "z3" ["-T:1", filePath] "") :: IO (Either SomeException (ExitCode, String, String))
  case result of
    Left _ -> return Unknown
    Right (_, output, _) ->
      case lines output of
        ("sat":_) -> return (Sat ())
        ("unsat":_) -> return (Unsat ())
        _ -> return Unknown

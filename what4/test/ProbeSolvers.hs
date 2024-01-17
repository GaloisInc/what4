{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ProbeSolvers where

import           Control.Exception ( try, SomeException )
import           Data.Char ( toLower )
import qualified Data.List as L
import           Data.Maybe ( catMaybes )
import           System.Exit ( ExitCode(..) )
import           System.Process ( readProcessWithExitCode )


newtype TestLevel = TestLevel String deriving Eq
newtype SolverName = SolverName String deriving (Eq, Show)
newtype SolverVersion = SolverVersion String deriving (Eq, Show)

getSolverVersion :: SolverName -> IO (Either String SolverVersion)
getSolverVersion (SolverName solver) =
  let args = case toLower <$> solver of
               -- n.b. abc will return a non-zero exit code if asked
               -- for command usage.
               "abc" -> ["s", "-q", "version;quit"]
               _ -> ["--version"]
  in try (readProcessWithExitCode (toLower <$> solver) args "") >>= \case
    Right (r,o,e) ->
      if r == ExitSuccess
      then let ol = lines o in
             return $ Right $ SolverVersion
             $ case ol of
                 [] -> solver <> " v??"
                 olh:_ -> olh
      else return $ Left $ solver <> " version error: " <> show r <> " /;/ " <> e
    Left (err :: SomeException) -> return $ Left $ solver <> " invocation error: " <> show err


reportSolverVersions :: TestLevel
                     -> (solverinfo -> SolverName)
                     -> [(solverinfo, Either String SolverVersion)]
                     -> IO [(solverinfo, SolverVersion)]
reportSolverVersions testLevel getSolverName versionedSolvers =
  do putStrLn "SOLVER SELF-REPORTED VERSIONS::"
     catMaybes <$> mapM (rep testLevel) versionedSolvers
  where rep lvl (testsolver, versionInfo) = let s = getSolverName testsolver
                                            in disp lvl testsolver s versionInfo
        disp lvl solver (SolverName sname) = \case
          Right v@(SolverVersion ver) ->
            do putStrLn $ "  Solver " <> sname <> " -> " <> ver
               return $ Just (solver, v)
          Left e -> if and [ "does not exist" `L.isInfixOf` e
                           , lvl == TestLevel "0"

                           ]
                    then do putStrLn $ "  Solver " <> sname <> " not found; skipping (would fail with CI_TEST_LEVEL=1)"
                            return Nothing
                    else do putStrLn $ "  Solver " <> sname <> " error: " <> e
                            return $ Just (solver, SolverVersion "v?")

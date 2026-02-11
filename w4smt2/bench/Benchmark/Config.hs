{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
module Benchmark.Config
  ( Config(..)
  , Solver(..)
  , parseArgs
  , solverCommand
  ) where

import GHC.Conc (numCapabilities)
import Options.Applicative qualified as Opt
import System.Process (CreateProcess, proc)

-- | Solver to run benchmarks with
data Solver
  = Z3           -- ^ External z3
  | Yices        -- ^ External yices
  | CVC5         -- ^ External cvc5
  | Bitwuzla     -- ^ External bitwuzla
  | W4           -- ^ w4smt2 (no external solver)
  | W4Z3         -- ^ w4smt2 z3
  | W4Yices      -- ^ w4smt2 yices
  | W4CVC5       -- ^ w4smt2 cvc5
  | W4Bitwuzla   -- ^ w4smt2 bitwuzla
  deriving (Eq, Ord, Show, Read)

data Config = Config
  { cfgCSVFile :: !FilePath
  , cfgDirectory :: !FilePath
  , cfgTimeout :: !Double
  , cfgWorkers :: !Int
  , cfgSolvers :: ![Solver]
  , cfgW4SMT2Path :: !FilePath
  , cfgLogFile :: !(Maybe FilePath)
  , cfgMaxSize :: !(Maybe Integer)
  }

parseArgs :: IO Config
parseArgs = do
  cfg <- Opt.execParser opts
  -- Default to [W4] if no solvers specified
  return cfg { cfgSolvers = if null (cfgSolvers cfg) then [W4] else cfgSolvers cfg }
  where
    opts = Opt.info (configParser Opt.<**> Opt.helper)
      ( Opt.fullDesc
     <> Opt.progDesc "Benchmark w4smt2 on a directory of .smt2 files"
      )

configParser :: Opt.Parser Config
configParser = Config
  Opt.<$> Opt.argument Opt.str
      ( Opt.metavar "CSV_FILE"
     <> Opt.help "CSV file to save/resume results"
      )
  Opt.<*> Opt.argument Opt.str
      ( Opt.metavar "DIRECTORY"
     <> Opt.help "Directory to search for .smt2 files"
      )
  Opt.<*> Opt.option Opt.auto
      ( Opt.long "timeout"
     <> Opt.short 't'
     <> Opt.metavar "SECONDS"
     <> Opt.value 10.0
     <> Opt.showDefault
     <> Opt.help "Timeout per file in seconds"
      )
  Opt.<*> Opt.option Opt.auto
      ( Opt.long "workers"
     <> Opt.short 'j'
     <> Opt.metavar "N"
     <> Opt.value numCapabilities
     <> Opt.showDefault
     <> Opt.help "Number of parallel workers"
      )
  Opt.<*> Opt.many solverOption
  Opt.<*> pure "w4smt2"
  Opt.<*> Opt.optional (Opt.strOption
      ( Opt.long "log-file"
     <> Opt.metavar "FILE"
     <> Opt.help "Write results to log file"
      ))
  Opt.<*> Opt.optional (Opt.option Opt.auto
      ( Opt.long "max-size"
     <> Opt.metavar "KB"
     <> Opt.help "Skip files larger than KB kilobytes"
      ))

solverOption :: Opt.Parser Solver
solverOption = Opt.option (Opt.str >>= parseSolver)
  ( Opt.long "solver"
  <> Opt.short 's'
  <> Opt.metavar "SOLVER"
  <> Opt.help "Solver to run (can be specified multiple times). Valid: z3, yices, cvc5, bitwuzla, w4, w4z3, w4yices, w4cvc5, w4bitwuzla"
  )
  where
    parseSolver = \case
      "z3" -> return Z3
      "yices" -> return Yices
      "cvc5" -> return CVC5
      "bitwuzla" -> return Bitwuzla
      "w4" -> return W4
      "w4z3" -> return W4Z3
      "w4yices" -> return W4Yices
      "w4cvc5" -> return W4CVC5
      "w4bitwuzla" -> return W4Bitwuzla
      s -> Opt.readerError $ "Unknown solver: " ++ s

-- | Get the command to run for a given solver
solverCommand :: Config -> Solver -> FilePath -> CreateProcess
solverCommand cfg solver file = case solver of
  Z3 -> proc "z3" [file]
  Yices -> proc "yices-smt2" [file]
  CVC5 -> proc "cvc5" [file]
  Bitwuzla -> proc "bitwuzla" [file]
  W4 -> proc (cfgW4SMT2Path cfg) [file]
  W4Z3 -> proc (cfgW4SMT2Path cfg) ["z3", file]
  W4Yices -> proc (cfgW4SMT2Path cfg) ["yices", file]
  W4CVC5 -> proc (cfgW4SMT2Path cfg) ["cvc5", file]
  W4Bitwuzla -> proc (cfgW4SMT2Path cfg) ["bitwuzla", file]

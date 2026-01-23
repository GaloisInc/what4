{-# LANGUAGE ImportQualifiedPost #-}
module Benchmark.Config
  ( Config(..)
  , parseArgs
  ) where

import GHC.Conc (numCapabilities)
import Options.Applicative qualified as Opt

data Config = Config
  { cfgDirectory :: !FilePath
  , cfgTimeout :: !Double
  , cfgWorkers :: !Int
  , cfgVerifyZ3 :: !Bool
  , cfgZ3Path :: !FilePath
  , cfgW4SMT2Path :: !FilePath
  , cfgLogFile :: !(Maybe FilePath)
  , cfgMaxSize :: !(Maybe Integer)
  }

parseArgs :: IO Config
parseArgs = Opt.execParser opts
  where
    opts = Opt.info (configParser Opt.<**> Opt.helper)
      ( Opt.fullDesc
     <> Opt.progDesc "Benchmark w4smt2 on a directory of .smt2 files"
      )

configParser :: Opt.Parser Config
configParser = Config
  Opt.<$> Opt.argument Opt.str
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
  Opt.<*> Opt.flag False True
      ( Opt.long "verify"
     <> Opt.help "Verify results with Z3"
      )
  Opt.<*> Opt.strOption
      ( Opt.long "z3-path"
     <> Opt.metavar "PATH"
     <> Opt.value "z3"
     <> Opt.showDefault
     <> Opt.help "Path to Z3 executable"
      )
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

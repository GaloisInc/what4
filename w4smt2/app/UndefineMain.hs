{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}

module Main (main) where

import System.Environment qualified as Env
import System.FilePath ((-<.>))
import System.IO qualified as IO
import System.Exit qualified as Exit
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text.IO
import W4SMT2.Parser qualified as Parser
import W4SMT2.Pretty qualified as Pretty
import W4SMT2.Unfold qualified as Unfold

main :: IO ()
main = do
  args <- Env.getArgs
  case args of
    [] -> do
      -- stdin -> stdout
      input <- Text.IO.getContents
      output <- processInput input
      Text.IO.putStr output
    [path] -> do
      -- file -> file.unfolded.smt2
      input <- Text.IO.readFile path
      output <- processInput input
      let outPath = path -<.> "unfolded.smt2"
      Text.IO.writeFile outPath output
      IO.hPutStrLn IO.stderr $ "Wrote: " ++ outPath
    _ -> do
      IO.hPutStrLn IO.stderr "Usage: undefine-fun [FILE]"
      Exit.exitFailure

processInput :: Text -> IO Text
processInput input = do
  let ?logStderr = Text.IO.hPutStrLn IO.stderr
  sexps <- Parser.parseSExps input
  unfolded <- Unfold.unfoldDefineFuns sexps
  return $ Text.unlines (map Pretty.ppSExp unfolded)

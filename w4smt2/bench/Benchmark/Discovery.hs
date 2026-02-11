{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
module Benchmark.Discovery
  ( findSmt2Files
  ) where

import Control.Monad (filterM)
import Data.List (sort)
import System.Directory (doesDirectoryExist, getFileSize, listDirectory, makeAbsolute)
import System.FilePath (takeExtension, (</>))

-- | Recursively find all .smt2 files in a directory
-- Optionally filters by max file size in KB
findSmt2Files :: FilePath -> Maybe Integer -> IO [FilePath]
findSmt2Files dir maxSizeKB = do
  absDir <- makeAbsolute dir
  exists <- doesDirectoryExist absDir
  if not exists
    then return []
    else do
      entries <- listDirectory absDir
      let fullPaths = map (absDir </>) entries
      (dirs, files) <- partitionM doesDirectoryExist fullPaths
      smt2Files <- filterM sizeOk (filter isSmt2File files)
      subFiles <- concat <$> mapM (\d -> findSmt2Files d maxSizeKB) dirs
      return $ sort (smt2Files ++ subFiles)
  where
    sizeOk :: FilePath -> IO Bool
    sizeOk path = case maxSizeKB of
      Nothing -> return True
      Just maxKB -> do
        fileSizeKB <- (`div` 1024) <$> getFileSize path
        return (fileSizeKB <= maxKB)

-- | Check if a file has .smt2 extension
isSmt2File :: FilePath -> Bool
isSmt2File path = takeExtension path == ".smt2"

-- | Partition a list based on a monadic predicate
partitionM :: Monad m => (a -> m Bool) -> [a] -> m ([a], [a])
partitionM f = \case
  [] -> return ([], [])
  x:xs -> do
    result <- f x
    (ys, ns) <- partitionM f xs
    return $ if result then (x:ys, ns) else (ys, x:ns)

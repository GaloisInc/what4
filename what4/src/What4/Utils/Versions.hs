{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module What4.Utils.Versions where

import qualified Config as Config
import           Control.Monad.IO.Class
import           Control.Exception (throw, throwIO)
import           Control.Monad (foldM)
import           Data.List (find)
import           Data.Text (Text)
import qualified Data.Text.IO as Text
import           Data.Versions (Version(..))
import qualified Data.Versions as Versions

import Paths_what4( getDataFileName )

import Language.Haskell.TH
import Language.Haskell.TH.Lift

-- NB, orphan instances :-(
deriving instance Lift Versions.VUnit
deriving instance Lift Versions.Version

ver :: Text -> Q Exp
ver nm =
  case Versions.version nm of
    Left err -> throw err
    Right v  -> lift v

data SolverBounds =
  SolverBounds
  { lower :: Maybe Version
  , upper :: Maybe Version
  , recommended :: Maybe Version
  }

deriving instance Lift SolverBounds

emptySolverBounds :: SolverBounds
emptySolverBounds = SolverBounds Nothing Nothing Nothing

-- | This method parses configuration files describing the
--   upper and lower bounds of solver versions we expect to
--   work correctly with What4.  See the file \"solverBounds.config\"
--   for examples of how such bounds are specified.
parseSolverBounds :: FilePath -> IO [(Text,SolverBounds)]
parseSolverBounds fname =
  do cf <- Config.parse <$> Text.readFile fname
     case cf of
       Left err -> throwIO err
       Right (Config.Sections _ ss)
         | Just Config.Section{ Config.sectionValue = Config.Sections _ vs } <-
                   find (\s -> Config.sectionName s == "solvers") ss
         -> mapM getSolverBound vs

       Right _ -> fail ("could not parse solver bounds from " ++ fname)

 where
   getSolverBound :: Config.Section Config.Position -> IO (Text, SolverBounds)
   getSolverBound Config.Section{ Config.sectionName = nm, Config.sectionValue = Config.Sections _ vs } =
     do b <- foldM updateBound emptySolverBounds vs
        pure (nm, b)
   getSolverBound v = fail ("could not parse solver bounds " ++ show v)


   updateBound :: SolverBounds -> Config.Section Config.Position -> IO SolverBounds
   updateBound bnd Config.Section{ Config.sectionName = nm, Config.sectionValue = Config.Text _ val} =
     case Versions.version val of
       Left err -> throwIO err
       Right v
         | nm == "lower"       -> pure bnd { lower = Just v }
         | nm == "upper"       -> pure bnd { upper = Just v }
         | nm == "recommended" -> pure bnd { recommended = Just v }
         | otherwise -> fail ("unrecognized solver bound name" ++ show nm)

   updateBound _ v = fail ("could not parse solver bound " ++ show v)


computeDefaultSolverBounds :: Q Exp
computeDefaultSolverBounds =
  lift =<< (liftIO (parseSolverBounds =<< getDataFileName "solverBounds.config"))

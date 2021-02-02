{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module What4.Utils.Versions where

import           Control.Exception (throw)
import           Data.Text (Text)
import           Data.Versions (Version(..))
import qualified Data.Versions as Versions

import Language.Haskell.TH
import Language.Haskell.TH.Lift

deriving instance Lift Versions.VUnit
deriving instance Lift Versions.Version

ver :: Text -> Q Exp
ver nm =
  case Versions.version nm of
    Left err -> throw err
    Right v  -> lift v


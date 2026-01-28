-----------------------------------------------------------------------
-- |
-- Module           : What4.ProgramLoc
-- Description      : Datatype for handling program locations
-- Copyright        : (c) Galois, Inc 2014-2020
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module primarily defines the `Position` datatype for
-- handling program location data.  A program location may refer
-- either to a source file location (file name, line and column number),
-- a binary file location (file name and byte offset) or be a dummy
-- "internal" location assigned to generated program fragments.
------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module What4.ProgramLoc
  ( Position(..)
  , sourcePos
  , startOfFile
  , ppNoFileName
  , Posd(..)
  , ProgramLoc
  , mkProgramLoc
  , initializationLoc
  , plFunction
  , plSourceLoc
    -- * Objects with a program location associated.
  , HasProgramLoc(..)
  ) where

import           Control.DeepSeq
import           Lens.Micro
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Word
import           Numeric (showHex)
import qualified Prettyprinter as PP

import           What4.FunctionName

------------------------------------------------------------------------
-- Position

data Position
     -- | A source position containing filename, line, and column.
   = SourcePos !Text !Int !Int
     -- | A binary position containing a filename and address in memory.
   | BinaryPos !Text !Word64
     -- | Some unstructured position information that doesn't fit into the other categories.
   | OtherPos !Text
     -- | Generated internally by the simulator, or otherwise unknown.
   | InternalPos
  deriving (Eq, Ord)

instance Show Position where
  show p = show (PP.pretty p)

instance NFData Position where
  rnf (SourcePos t l c) = rnf (t,l,c)
  rnf (BinaryPos t a)   = rnf (t,a)
  rnf (OtherPos t)      = rnf t
  rnf InternalPos       = ()

sourcePos :: FilePath -> Int -> Int -> Position
sourcePos p l c = SourcePos (Text.pack p) l c

startOfFile :: FilePath -> Position
startOfFile path = sourcePos path 1 0

instance PP.Pretty Position where
  pretty (SourcePos path l c) =
    PP.pretty path
      PP.<> PP.colon PP.<> PP.pretty l
      PP.<> PP.colon PP.<> PP.pretty c
  pretty (BinaryPos path addr) =
    PP.pretty path PP.<> PP.colon PP.<>
      PP.pretty "0x" PP.<> PP.pretty (showHex addr "")
  pretty (OtherPos txt) = PP.pretty txt
  pretty InternalPos = PP.pretty "internal"

ppNoFileName :: Position -> PP.Doc ann
ppNoFileName (SourcePos _ l c) =
  PP.pretty l PP.<> PP.colon PP.<> PP.pretty c
ppNoFileName (BinaryPos _ addr) =
  PP.pretty (showHex addr "")
ppNoFileName (OtherPos msg) =
  PP.pretty msg
ppNoFileName InternalPos = PP.pretty "internal"

------------------------------------------------------------------------
-- Posd

-- | A value with a source position associated.
data Posd v = Posd { pos :: !Position
                   , pos_val :: !v
                   }
  deriving (Functor, Foldable, Traversable, Show, Eq)

instance NFData v => NFData (Posd v) where
  rnf p = rnf (pos p, pos_val p)

------------------------------------------------------------------------
-- ProgramLoc

-- | A very small type that contains a function and PC identifier.
data ProgramLoc
   = ProgramLoc { plFunction :: {-# UNPACK #-} !FunctionName
                , plSourceLoc :: !Position
                }
 deriving (Show, Eq, Ord)

-- | Location for initialization code
initializationLoc :: ProgramLoc
initializationLoc = ProgramLoc startFunctionName (startOfFile "")

-- | Make a program loc
mkProgramLoc :: FunctionName
             -> Position
             -> ProgramLoc
mkProgramLoc = ProgramLoc

------------------------------------------------------------------------
-- HasProgramLoc

class HasProgramLoc v where
  programLoc :: Lens' v ProgramLoc

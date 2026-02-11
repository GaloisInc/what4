{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module W4SMT2.Pretty
  ( ppSExp
  , userErr
  , unsupported
  ) where

import Data.Text (Text)
import Data.Text qualified as Text
import Prettyprinter qualified as PP
import Prettyprinter.Render.Text qualified as PP
import System.Exit qualified as Exit

import What4.Protocol.SExp qualified as SExp

-- | Pretty-print an S-expression
ppSExp :: SExp.SExp -> Text
ppSExp = \case
  SExp.SAtom t -> t
  SExp.SString t -> "\"" <> t <> "\""
  SExp.SApp [] -> "()"
  SExp.SApp xs -> "(" <> Text.intercalate " " (map ppSExp xs) <> ")"

-- | Report a user error and exit with code 1
userErr :: (?logStderr :: Text -> IO ()) => PP.Doc ann -> IO a
userErr doc = do
  let msg = PP.renderStrict (PP.layoutCompact (PP.pretty ("user error:" :: Text) PP.<+> doc))
  ?logStderr msg
  Exit.exitWith (Exit.ExitFailure 1)

-- | Report an unsupported feature and exit with code 2
unsupported :: (?logStderr :: Text -> IO ()) => PP.Doc ann -> IO a
unsupported doc = do
  let msg = PP.renderStrict (PP.layoutCompact (PP.pretty ("unsupported:" :: Text) PP.<+> doc))
  ?logStderr msg
  Exit.exitWith (Exit.ExitFailure 2)

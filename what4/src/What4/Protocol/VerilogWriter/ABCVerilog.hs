{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-
Module           : What4.Protocol.VerilogWriter.Export.ABCVerilog
Copyright        : (c) Galois, Inc 2020
Maintainer       : Aaron Tomb <atomb@galois.com>
License          : BSD3

Export Verilog in the particular syntax ABC supports.
-}

module What4.Protocol.VerilogWriter.ABCVerilog where

import Data.Parameterized.NatRepr
import Data.Parameterized.Some
import Data.Text.Prettyprint.Doc
import What4.BaseTypes
import What4.Protocol.VerilogWriter.AST
import Prelude hiding ((<$>))
import Numeric (showHex)

moduleDoc :: Module n -> Doc () -> Doc ()
moduleDoc (Module ms) name =
  vsep
    [ nest 2 $ vsep
      [ "module" <+> name <> tupled params <> semi
      , vsep (map inputDoc (reverse (vsInputs ms)))
      , vsep (map (wireDoc "wire") (reverse (vsWires ms)))
      , vsep (map (wireDoc "output") (reverse (vsOutputs ms)))
      ]
    , "endmodule"
    ]
  where
    inputNames = map (identDoc . snd) (vsInputs ms)
    outputNames = map (identDoc . (\(_, n, _) -> n)) (vsOutputs ms)
    params = reverse inputNames ++ reverse outputNames

typeDoc :: Doc () -> BaseTypeRepr tp -> Doc ()
typeDoc ty BaseBoolRepr = ty
typeDoc ty (BaseBVRepr w) =
  ty <+> lbracket <> pretty (intValue w - 1) <> ":0" <> rbracket
typeDoc _ _ = "<type error>"

identDoc :: Identifier -> Doc ()
identDoc = pretty

lhsDoc :: LHS -> Doc ()
lhsDoc (LHS name) = identDoc name
lhsDoc (LHSBit name idx) =
  identDoc name <> lbracket <> pretty idx <> rbracket

inputDoc :: (Some BaseTypeRepr, Identifier) -> Doc ()
inputDoc (tp, name) =
  viewSome (typeDoc "input") tp <+> identDoc name <> semi

wireDoc :: Doc () -> (Some BaseTypeRepr, Identifier, Some Exp) -> Doc ()
wireDoc ty (tp, name, e) =
  viewSome (typeDoc ty) tp <+> identDoc name <+> equals <+> viewSome expDoc e <> semi

unopDoc :: Unop tp -> Doc ()
unopDoc = pretty . showUnop

binopDoc :: Binop inTp outTp -> Doc ()
binopDoc = pretty . showBinop

-- | Show non-negative Integral numbers in base 16.
hexDoc :: Integer -> Integer -> Doc ()
hexDoc _ n = pretty $ showHex n ""

iexpDoc :: IExp tp -> Doc ()
iexpDoc (Ident _ name) = identDoc name

expDoc :: Exp tp -> Doc ()
expDoc (IExp e) = iexpDoc e
expDoc (Binop op l r) = iexpDoc l <+> binopDoc op <+> iexpDoc r
expDoc (Unop op e) = unopDoc op <+> iexpDoc e
-- NB: special pretty-printer because ABC has a hack to detect this specific syntax
expDoc (BVRotateL (intValue -> w) e n) =
  parens (v <+> "<<" <+> pretty n) <+> "|" <+>
  parens (v <+> ">>" <+> parens (pretty w <+> "-" <+> pretty n))
    where v = iexpDoc e
-- NB: special pretty-printer because ABC has a hack to detect this specific syntax
expDoc (BVRotateR (intValue -> w) e n) =
  parens (v <+> ">>" <+> pretty n) <+> "|" <+>
  parens (v <+> "<<" <+> parens (pretty w <+> "-" <+> pretty n))
    where v = iexpDoc e
expDoc (Mux c t e) = iexpDoc c <+> "?" <+> iexpDoc t <+> colon <+> iexpDoc e
expDoc (Bit e i) =
  iexpDoc e <> lbracket <> pretty i <> rbracket
expDoc (BitSelect e (intValue -> start) (intValue -> len)) =
  iexpDoc e <> lbracket
            <> pretty (start + (len - 1))
            <> colon
            <> pretty start
            <> rbracket
expDoc (Concat _ es) = encloseSep lbrace rbrace comma (map (viewSome iexpDoc) es)
expDoc (BVLit w n) = pretty w' <> "'h" <> hexDoc w' n
  where w' = intValue w
expDoc (BoolLit True) = "1'b1"
expDoc (BoolLit False) = "1'b0"

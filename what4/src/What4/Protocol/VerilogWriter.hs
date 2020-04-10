{-
Module           : What4.Protocol.VerilogWriter.AST
Copyright        : (c) Galois, Inc 2020
Maintainer       : Jennifer Paykin <jpaykin@galois.com>
License          : BSD3

Connecting the Crucible simple builder backend to Verilog that can be read by
ABC.
-}

module What4.Protocol.VerilogWriter
  ( Module
  , exprVerilog
  , eqVerilog
  , exprToModule
  , eqToModule
  ) where

import Control.Monad.Except
import Data.Text.Prettyprint.Doc
import What4.Expr.Builder (Expr)

import What4.Protocol.VerilogWriter.AST
import What4.Protocol.VerilogWriter.ABCVerilog
import What4.Protocol.VerilogWriter.Backend

-- | Convert the What4 epxression into a Verilog module of the name given
exprVerilog :: Expr n tp -> Doc () -> ExceptT String IO (Doc ())
exprVerilog e name = fmap (\m -> moduleDoc m name) (exprToModule e)

eqVerilog :: Expr n tp -> Expr n tp -> Doc () -> ExceptT String IO (Doc ())
eqVerilog x y name =  fmap (\m -> moduleDoc m name) (eqToModule x y)

exprToModule :: Expr n tp -> ExceptT String IO (Module n)
exprToModule e = mkModule $ exprToVerilogExpr e

eqToModule :: Expr n tp -> Expr n tp -> ExceptT String IO (Module n)
eqToModule x y = mkModule $ eqToVerilogExpr x y

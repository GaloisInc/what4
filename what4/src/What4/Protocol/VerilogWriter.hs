{-# LANGUAGE TypeFamilies #-}
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
import Prettyprinter
import What4.Expr.Builder (Expr, SymExpr)
import What4.Interface (IsExprBuilder)

import What4.Protocol.VerilogWriter.AST
import What4.Protocol.VerilogWriter.ABCVerilog
import What4.Protocol.VerilogWriter.Backend

-- | Convert the given What4 expression into a textual representation of
-- a Verilog module of the given name.
exprVerilog ::
  (IsExprBuilder sym, SymExpr sym ~ Expr n) =>
  sym ->
  Expr n tp ->
  Doc () ->
  ExceptT String IO (Doc ())
exprVerilog sym e name = fmap (\m -> moduleDoc m name) (exprToModule sym e)

-- | Convert a statement of equality between the two given What4
-- expressions into the textual representation of a Verilog module of
-- the given name.
eqVerilog ::
  (IsExprBuilder sym, SymExpr sym ~ Expr n) =>
  sym ->
  Expr n tp ->
  Expr n tp ->
  Doc () ->
  ExceptT String IO (Doc ())
eqVerilog sym x y name =  fmap (\m -> moduleDoc m name) (eqToModule sym x y)

-- | Convert the given What4 expression into a Verilog module of the
-- given name.
exprToModule ::
  (IsExprBuilder sym, SymExpr sym ~ Expr n) =>
  sym ->
  Expr n tp ->
  ExceptT String IO (Module sym n)
exprToModule sym e = mkModule sym $ exprToVerilogExpr e

-- | Convert a statement of equality between the two given What4
-- expressions into a Verilog module of the given name.
eqToModule ::
  (IsExprBuilder sym, SymExpr sym ~ Expr n) =>
  sym ->
  Expr n tp ->
  Expr n tp ->
  ExceptT String IO (Module sym n)
eqToModule sym x y = mkModule sym $ eqToVerilogExpr x y

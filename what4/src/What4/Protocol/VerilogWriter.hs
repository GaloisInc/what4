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
  , exprsVerilog
  , exprsToModule
  ) where

import Control.Monad.Except
import Data.Parameterized.Some (Some(..), traverseSome)
import Prettyprinter
import What4.Expr.Builder (Expr, SymExpr)
import What4.Interface (IsExprBuilder)

import What4.Protocol.VerilogWriter.AST
import What4.Protocol.VerilogWriter.ABCVerilog
import What4.Protocol.VerilogWriter.Backend

-- | Convert the given What4 expressions, representing the outputs of a
-- circuit, into a textual representation of a Verilog module of the
-- given name.
exprsVerilog ::
  (IsExprBuilder sym, SymExpr sym ~ Expr n) =>
  sym ->
  [Some (Expr n)] ->
  Doc () ->
  ExceptT String IO (Doc ())
exprsVerilog sym es name = fmap (\m -> moduleDoc m name) (exprsToModule sym es)

-- | Convert the given What4 expressions, representing the outputs of a
-- circuit, into a Verilog module of the given name.
exprsToModule ::
  (IsExprBuilder sym, SymExpr sym ~ Expr n) =>
  sym ->
  [Some (Expr n)] ->
  ExceptT String IO (Module sym n)
exprsToModule sym es = mkModule sym $ map (traverseSome exprToVerilogExpr) es

{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module W4SMT2.Exec
  ( SolverState(..)
  , initState
  , execCommands
  , execCommand
  ) where

import Control.Monad qualified as Monad
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Parameterized.Context qualified as Ctx
import Data.Parameterized.Context (pattern (:>))
import Data.Parameterized.Some (Some(Some))
import Data.Text (Text)
import Data.Text qualified as Text
import Prettyprinter ((<+>))
import Prettyprinter qualified as PP

import What4.BaseTypes qualified as WBT
import What4.Interface qualified as WI
import What4.Protocol.SExp qualified as SExp
import What4.SatResult qualified as WSR

import W4SMT2.Parser (VarName(VarName), FnName(FnName, unFnName), ParamName(unParamName))
import W4SMT2.Parser qualified as Parser
import W4SMT2.Pretty qualified as Pretty
import W4SMT2.SExpPat (sexp)

data SolverState sym = SolverState
  { ssVars :: Map VarName (Some (WI.SymExpr sym))
  , ssFuns :: Map FnName (WI.SomeSymFn sym)
  , ssAsserts :: [WI.Pred sym]
  }

initState :: SolverState sym
initState = SolverState Map.empty Map.empty []

buildDefinedFn ::
  forall sym.
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  FnName ->
  [(ParamName, Some WBT.BaseTypeRepr)] ->
  Some WBT.BaseTypeRepr ->
  SExp.SExp ->
  Map VarName (Some (WI.SymExpr sym)) ->
  IO (WI.SomeSymFn sym)
buildDefinedFn sym fnName params (Some retType) body vars =
  buildParams Ctx.Empty vars params
  where
    buildParams ::
      forall ctx.
      Ctx.Assignment (WI.BoundVar sym) ctx ->
      Map VarName (Some (WI.SymExpr sym)) ->
      [(ParamName, Some WBT.BaseTypeRepr)] ->
      IO (WI.SomeSymFn sym)
    buildParams builtParams extendedVars = \case
      [] -> do
        Some bodyExpr <- Parser.parseExpr sym extendedVars Map.empty body
        let bodyType = WI.exprType bodyExpr
        case WBT.testEquality bodyType retType of
          Just WBT.Refl -> do
            let nm = WI.safeSymbol (Text.unpack (unFnName fnName))
            fn <- WI.definedFn
                    sym
                    nm
                    builtParams
                    bodyExpr
                    WI.AlwaysUnfold
            return (WI.SomeSymFn fn)
          Nothing ->
            Pretty.userErr $
              "define-fun body type mismatch: expected" <+> PP.viaShow retType
              <+> "but got" <+> PP.viaShow bodyType
      (paramName, Some paramType) : rest -> do
        let nm = WI.safeSymbol (Text.unpack (unParamName paramName))
        boundVar <- WI.freshBoundVar sym nm paramType
        let varExpr = WI.varExpr sym boundVar
        let newVars = Map.insert (VarName (unParamName paramName)) (Some varExpr) extendedVars
        buildParams (builtParams :> boundVar) newVars rest

-- | Execute commands and return the result of check-sat
execCommands ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  SolverState sym ->
  [SExp.SExp] ->
  IO (WSR.SatResult () ())
execCommands sym state = \case
  [] -> return WSR.Unknown
  (cmd:rest) -> do
    result <- execCommand sym state cmd
    case result of
      Left satResult -> return satResult
      Right newState -> execCommands sym newState rest

-- | Execute a single command
execCommand ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  SolverState sym ->
  SExp.SExp ->
  IO (Either (WSR.SatResult () ()) (SolverState sym))
execCommand sym state = \case
  [sexp|(declare-const #nameSexp #typeSexp)|]
    | SExp.SAtom name <- nameSexp -> do
        Some tp <- Parser.parseType typeSexp
        var <- WI.freshConstant sym (WI.safeSymbol (Text.unpack name)) tp
        return $ Right state { ssVars = Map.insert (VarName name) (Some var) (ssVars state) }

  [sexp|(declare-fun #nameSexp () #typeSexp)|]
    | SExp.SAtom name <- nameSexp -> do
        Some tp <- Parser.parseType typeSexp
        var <- WI.freshConstant sym (WI.safeSymbol (Text.unpack name)) tp
        return $ Right state { ssVars = Map.insert (VarName name) (Some var) (ssVars state) }

  [sexp|(define-fun #nameSexp #paramsSexp #retTypeSexp #body)|]
    | SExp.SAtom name <- nameSexp -> do
        params <- Parser.parseDefunParams paramsSexp
        retType <- Parser.parseType retTypeSexp
        fn <- buildDefinedFn sym (FnName name) params retType body (ssVars state)
        return $ Right state { ssFuns = Map.insert (FnName name) fn (ssFuns state) }

  [sexp|(assert #exprSexp)|] -> do
    Some expr <- Parser.parseExpr sym (ssVars state) (ssFuns state) exprSexp
    case WBT.testEquality (WI.exprType expr) WBT.BaseBoolRepr of
      Just WBT.Refl -> return $ Right state { ssAsserts = expr : ssAsserts state }
      Nothing -> Pretty.userErr $
        "assert requires Bool expression, got" <+> PP.viaShow (WI.exprType expr)

  [sexp|(check-sat)|] -> do
    result <- checkSat sym (ssAsserts state)
    return $ Left result

  [sexp|(exit)|] -> return $ Left WSR.Unknown

  -- Ignored commands (no-ops)
  [sexp|(set-info ..._)|] -> return $ Right state
  [sexp|(set-logic ..._)|] -> return $ Right state

  -- Unsupported commands
  SExp.SApp (SExp.SAtom cmd : _)
    | cmd `elem` unsupportedCommands ->
        Pretty.unsupported $ "command:" <+> PP.pretty cmd

  other -> Pretty.unsupported $ "command:" <+> PP.pretty (Pretty.ppSExp other)

unsupportedCommands :: [Text]
unsupportedCommands =
  ["push", "pop", "get-model", "get-value", "echo", "set-option"]

-- | Check satisfiability by examining if assertions simplify to constants
checkSat :: WI.IsSymExprBuilder sym => sym -> [WI.Pred sym] -> IO (WSR.SatResult () ())
checkSat sym preds = do
  conjunction <- Monad.foldM (WI.andPred sym) (WI.truePred sym) preds
  case WI.asConstantPred conjunction of
    Just True -> return (WSR.Sat ())
    Just False -> return (WSR.Unsat ())
    Nothing -> return WSR.Unknown

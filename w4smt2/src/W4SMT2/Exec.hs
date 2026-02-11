{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module W4SMT2.Exec
  ( SolverState(..)
  , initState
  , execCommands
  , execCommand
  , ExecutionResult(..)
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
import W4SMT2.SomeExpr (SomeExpr(SomeExpr))

data SolverState sym = SolverState
  { ssVars :: Map VarName (SomeExpr sym)
  , ssFuns :: Map FnName (WI.SomeSymFn sym)
  , ssAsserts :: [WI.Pred sym]
  , ssStack :: [StackFrame sym]  -- Stack for push/pop
  }

-- | A stack frame for push/pop
data StackFrame sym = StackFrame
  { sfVars :: Map VarName (SomeExpr sym)
  , sfFuns :: Map FnName (WI.SomeSymFn sym)
  , sfAsserts :: [WI.Pred sym]
  }

-- | Result of executing commands (may contain multiple check-sat results)
newtype ExecutionResult = ExecutionResult
  { erResults :: [WSR.SatResult () ()]  -- All check-sat results in order
  }
  deriving (Show)

initState :: SolverState sym
initState = SolverState Map.empty Map.empty [] []

buildDefinedFn ::
  forall sym.
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  FnName ->
  [(ParamName, Some WBT.BaseTypeRepr)] ->
  Some WBT.BaseTypeRepr ->
  SExp.SExp ->
  Map VarName (SomeExpr sym) ->
  Map FnName (WI.SomeSymFn sym) ->
  IO (WI.SomeSymFn sym)
buildDefinedFn sym fnName params (Some retType) body vars fns =
  buildParams Ctx.Empty vars params
  where
    buildParams ::
      forall ctx.
      Ctx.Assignment (WI.BoundVar sym) ctx ->
      Map VarName (SomeExpr sym) ->
      [(ParamName, Some WBT.BaseTypeRepr)] ->
      IO (WI.SomeSymFn sym)
    buildParams builtParams extendedVars = \case
      [] -> do
        SomeExpr bodyExpr <- Parser.parseExpr sym extendedVars fns body
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
        let varNm = VarName (unParamName paramName)
        let newVars = Map.insert varNm (SomeExpr varExpr) extendedVars
        buildParams (builtParams :> boundVar) newVars rest

buildUninterpFn ::
  forall sym.
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  FnName ->
  [Some WBT.BaseTypeRepr] ->
  Some WBT.BaseTypeRepr ->
  IO (WI.SomeSymFn sym)
buildUninterpFn sym fnName paramTypes (Some retType) =
  buildParams Ctx.Empty paramTypes
  where
    buildParams ::
      forall ctx.
      Ctx.Assignment WBT.BaseTypeRepr ctx ->
      [Some WBT.BaseTypeRepr] ->
      IO (WI.SomeSymFn sym)
    buildParams builtParams = \case
      [] -> do
        let nm = WI.safeSymbol (Text.unpack (unFnName fnName))
        fn <- WI.freshTotalUninterpFn sym nm builtParams retType
        return (WI.SomeSymFn fn)
      (Some paramType) : rest ->
        buildParams (builtParams :> paramType) rest

-- | Execute commands and return all check-sat results
execCommands ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  SolverState sym ->
  Maybe (sym -> [WI.Pred sym] -> IO (WSR.SatResult () ())) ->
  [SExp.SExp] ->
  IO ExecutionResult
execCommands sym state maybeSolverCallback = loop state []
  where
    loop _ results [] = return $ ExecutionResult (reverse results)
    loop st results (cmd:rest) = do
      maybeResult <- execCommand sym st maybeSolverCallback cmd
      case maybeResult of
        Nothing -> return $ ExecutionResult (reverse results)  -- exit encountered, stop
        Just (Left satResult) ->
          -- Accumulate this check-sat result
          loop st (satResult : results) rest
        Just (Right newState) -> loop newState results rest

-- | Execute a single command
-- Returns Nothing if exit was encountered (stop processing)
-- Returns Just (Left result) if check-sat was encountered (output result and continue)
-- Returns Just (Right newState) if other command was executed (continue)
execCommand ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  SolverState sym ->
  Maybe (sym -> [WI.Pred sym] -> IO (WSR.SatResult () ())) ->
  SExp.SExp ->
  IO (Maybe (Either (WSR.SatResult () ()) (SolverState sym)))
execCommand sym state maybeSolverCallback = \case
  [sexp|(declare-const #nameSexp #typeSexp)|]
    | SExp.SAtom name <- nameSexp -> do
        Some tp <- Parser.parseType typeSexp
        var <- WI.freshConstant sym (WI.safeSymbol (Text.unpack name)) tp
        return $ Just $ Right state { ssVars = Map.insert (VarName name) (SomeExpr var) (ssVars state) }

  [sexp|(declare-fun #nameSexp #paramsSexp #typeSexp)|]
    | SExp.SAtom name <- nameSexp -> do
        params <- Parser.parseDeclareFunParams paramsSexp
        case params of
          [] -> do
            -- Zero-arity: treat as constant
            Some tp <- Parser.parseType typeSexp
            var <- WI.freshConstant sym (WI.safeSymbol (Text.unpack name)) tp
            return $ Just $ Right state { ssVars = Map.insert (VarName name) (SomeExpr var) (ssVars state) }
          _ -> do
            -- Non-zero arity: create uninterpreted function
            retType <- Parser.parseType typeSexp
            fn <- buildUninterpFn sym (FnName name) params retType
            return $ Just $ Right state { ssFuns = Map.insert (FnName name) fn (ssFuns state) }

  [sexp|(define-fun #nameSexp #paramsSexp #retTypeSexp #body)|]
    | SExp.SAtom name <- nameSexp -> do
        params <- Parser.parseDefunParams paramsSexp
        retType <- Parser.parseType retTypeSexp
        fn <- buildDefinedFn sym (FnName name) params retType body (ssVars state) (ssFuns state)
        return $ Just $ Right state { ssFuns = Map.insert (FnName name) fn (ssFuns state) }

  [sexp|(assert #exprSexp)|] -> do
    SomeExpr expr <- Parser.parseExpr sym (ssVars state) (ssFuns state) exprSexp
    case WBT.testEquality (WI.exprType expr) WBT.BaseBoolRepr of
      Just WBT.Refl -> return $ Just $ Right state { ssAsserts = expr : ssAsserts state }
      Nothing -> Pretty.userErr $
        "assert requires Bool expression, got" <+> PP.viaShow (WI.exprType expr)

  [sexp|(push $n)|] -> do
    let numLevels = fromIntegral @Integer @Int n
    if numLevels <= 0
      then Pretty.userErr "push requires a positive integer"
      else do
        -- Create a stack frame capturing the current state
        let frame = StackFrame
              { sfVars = ssVars state
              , sfFuns = ssFuns state
              , sfAsserts = ssAsserts state
              }
        -- Push the same frame N times (each push saves the current state)
        -- This is correct because between multiple push(N) calls with N>1,
        -- the state doesn't change, so saving it N times is equivalent
        let newStack = replicate numLevels frame ++ ssStack state
        return $ Just $ Right state { ssStack = newStack }

  [sexp|(pop $n)|] -> do
    let numLevels = fromIntegral @Integer @Int n
    if numLevels <= 0
      then Pretty.userErr "pop requires a positive integer"
      else if numLevels > length (ssStack state)
        then Pretty.userErr $ "cannot pop" <+> PP.viaShow numLevels <+> "levels (only" <+> PP.viaShow (length (ssStack state)) <+> "available)"
        else do
          let (framesToPop, newStack) = splitAt numLevels (ssStack state)
          case framesToPop of
            [] -> Pretty.userErr "internal error: no frames to pop"
            (topFrame : _) -> return $ Just $ Right state
              { ssVars = sfVars topFrame
              , ssFuns = sfFuns topFrame
              , ssAsserts = sfAsserts topFrame
              , ssStack = newStack
              }

  [sexp|(check-sat)|] -> do
    internalResult <- checkSat sym (ssAsserts state)
    finalResult <- case (internalResult, maybeSolverCallback) of
      (WSR.Unknown, Just callback) -> callback sym (ssAsserts state)
      _ -> return internalResult
    return $ Just $ Left finalResult

  [sexp|(exit)|] ->
    -- Stop processing commands
    return Nothing

  -- Ignored commands (no-ops)
  [sexp|(set-info ..._)|] -> return $ Just $ Right state
  [sexp|(set-logic ..._)|] -> return $ Just $ Right state

  -- Unsupported commands
  SExp.SApp (SExp.SAtom cmd : _)
    | cmd `elem` unsupportedCommands ->
        Pretty.unsupported $ "command:" <+> PP.pretty cmd

  other -> Pretty.unsupported $ "command:" <+> PP.pretty (Pretty.ppSExp other)

unsupportedCommands :: [Text]
unsupportedCommands =
  ["get-model", "get-value", "echo", "set-option"]

-- | Check satisfiability by examining if assertions simplify to constants
checkSat :: WI.IsSymExprBuilder sym => sym -> [WI.Pred sym] -> IO (WSR.SatResult () ())
checkSat sym preds = do
  conjunction <- Monad.foldM (WI.andPred sym) (WI.truePred sym) preds
  case WI.asConstantPred conjunction of
    Just True -> return (WSR.Sat ())
    Just False -> return (WSR.Unsat ())
    Nothing -> return WSR.Unknown

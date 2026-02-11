{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wno-error=overlapping-patterns #-}  -- ghc 9.10.1 bug

module W4SMT2.Parser
  ( VarName(..)
  , FnName(..)
  , ParamName(..)
  , parseSExps
  , parseType
  , parseExpr
  , parseBoolExpr
  , parseDefunParams
  , parseDeclareFunParams
  ) where

import Control.Applicative ((<|>))
import Control.Monad (forM)
import Control.Monad qualified as Monad
import Data.Attoparsec.Text qualified as A
import Data.BitVector.Sized qualified as BV
import Data.List (isPrefixOf)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Ratio ((%))
import Data.String (IsString)
import Numeric.Natural (Natural)
import Data.Parameterized.Context qualified as Ctx
import Data.Parameterized.Context (pattern (:>))
import Data.Parameterized.NatRepr qualified as NatRepr
import Data.Parameterized.Some (Some(Some))
import GHC.TypeLits (type (<=))
import Data.Text (Text)
import Data.Text qualified as Text
import Prettyprinter ((<+>))
import Prettyprinter qualified as PP
import System.Exit qualified as Exit

import What4.BaseTypes qualified as WBT
import What4.Interface qualified as WI
import What4.Protocol.SExp qualified as SExp

import W4SMT2.Pretty qualified as Pretty
import W4SMT2.SExpPat (sexp)
import W4SMT2.SomeExpr (SomeExpr(SomeExpr))

-- | Variable name
newtype VarName = VarName { unVarName :: Text }
  deriving (Eq, Ord, Show, IsString)

-- | Function name
newtype FnName = FnName { unFnName :: Text }
  deriving (Eq, Ord, Show, IsString)

-- | Parameter name
newtype ParamName = ParamName { unParamName :: Text }
  deriving (Eq, Ord, Show, IsString)

-- | Parse multiple S-expressions from text
parseSExps :: (?logStderr :: Text -> IO ()) => Text -> IO [SExp.SExp]
parseSExps input =
  case A.parseOnly parser input of
    Left err -> do
      ?logStderr ("Parse error: " <> Text.pack err)
      Exit.exitFailure
    Right sexps -> return sexps
  where
    parser = skipSpaceAndComments *> A.many' (SExp.parseSExp readString <* skipSpaceAndComments) <* A.endOfInput

    skipSpaceAndComments :: A.Parser ()
    skipSpaceAndComments = A.skipWhile (\c -> c `elem` (" \t\n\r" :: String)) <* A.skipMany comment
      where
        comment = A.char ';' *> A.skipWhile (/= '\n') *> (A.char '\n' >> pure () <|> pure ())

    readString :: A.Parser Text
    readString = do
      _ <- A.char '"'
      s <- A.takeWhile (/= '"')
      _ <- A.char '"'
      return s

-- | Parse a type s-expression
parseType :: (?logStderr :: Text -> IO ()) => SExp.SExp -> IO (Some WBT.BaseTypeRepr)
parseType sexp' = case sexp' of
  [sexp|Bool|] -> return $ Some WBT.BaseBoolRepr
  [sexp|Int|] -> return $ Some WBT.BaseIntegerRepr
  [sexp|Real|] -> return $ Some WBT.BaseRealRepr
  [sexp|(#_ BitVec $n)|]
    | Some w <- NatRepr.mkNatRepr (fromIntegral @Integer @Natural n)
    , Just NatRepr.LeqProof <- NatRepr.testLeq (NatRepr.knownNat @1) w ->
      return $ Some $ WBT.BaseBVRepr w
  _ -> Pretty.unsupported $ "type:" <+> PP.pretty (Pretty.ppSExp sexp')

-- | Parse let bindings
parseLetBindings ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  Map VarName (SomeExpr sym) ->
  SExp.SExp ->
  IO [(VarName, SomeExpr sym)]
parseLetBindings sym vars (SExp.SApp bindingPairs) = do
  forM bindingPairs $ \case
    [sexp|(#varName #exprSExp)|]
      | SExp.SAtom name <- varName -> do
          SomeExpr expr <- parseExpr sym vars Map.empty exprSExp
          return (VarName name, SomeExpr expr)
    other -> Pretty.userErr $ "invalid let binding:" <+> PP.pretty (Pretty.ppSExp other)
parseLetBindings _ _ other =
  Pretty.userErr $ "let bindings must be a list:" <+> PP.pretty (Pretty.ppSExp other)

-- | Parse define-fun parameter list
parseDefunParams ::
  (?logStderr :: Text -> IO ()) =>
  SExp.SExp ->
  IO [(ParamName, Some WBT.BaseTypeRepr)]
parseDefunParams = \case
  SExp.SApp params ->
    forM params $ \case
      [sexp|(#nameSexp #typeSexp)|]
        | SExp.SAtom name <- nameSexp -> do
            tp <- parseType typeSexp
            return (ParamName name, tp)
      other -> Pretty.userErr $
        "invalid define-fun parameter:" <+> PP.pretty (Pretty.ppSExp other)
  other ->
    Pretty.userErr $
      "define-fun parameters must be a list:" <+> PP.pretty (Pretty.ppSExp other)

-- | Parse declare-fun parameter types (types only, no names)
parseDeclareFunParams ::
  (?logStderr :: Text -> IO ()) =>
  SExp.SExp ->
  IO [Some WBT.BaseTypeRepr]
parseDeclareFunParams = \case
  SExp.SApp typeList ->
    forM typeList parseType
  other ->
    Pretty.userErr $
      "declare-fun parameters must be a list of types:" <+> PP.pretty (Pretty.ppSExp other)

-- | Apply a function with dynamic argument list and type checking
applyFunction ::
  forall sym.
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  Map VarName (SomeExpr sym) ->
  Map FnName (WI.SomeSymFn sym) ->
  WI.SomeSymFn sym ->
  [SExp.SExp] ->
  IO (SomeExpr sym)
applyFunction sym vars fns (WI.SomeSymFn fn) argSexps = do
  args <- buildArgs (WI.fnArgTypes fn) (reverse argSexps)
  result <- WI.applySymFn sym fn args
  return (SomeExpr result)
  where
    buildArgs ::
      forall ctx.
      Ctx.Assignment WBT.BaseTypeRepr ctx ->
      [SExp.SExp] ->
      IO (Ctx.Assignment (WI.SymExpr sym) ctx)
    buildArgs = \cases
      Ctx.Empty [] -> return Ctx.Empty
      (restTps :> tp) (argSexp : rest) -> do
        restArgs <- buildArgs restTps rest
        SomeExpr arg <- parseExpr sym vars fns argSexp
        case WBT.testEquality (WI.exprType arg) tp of
          Just WBT.Refl ->
            return (restArgs :> arg)
          Nothing ->
            Pretty.userErr $
              "function argument type mismatch: expected" <+> PP.viaShow tp
              <+> "but got" <+> PP.viaShow (WI.exprType arg)
      _ _ ->
        Pretty.userErr "function arity mismatch"

parseAtom ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  Map VarName (SomeExpr sym) ->
  Map FnName (WI.SomeSymFn sym) ->
  Text ->
  IO (Maybe (SomeExpr sym))
parseAtom sym vars fns name = do
  case Map.lookup (VarName name) vars of
    Just var -> return (Just var)
    Nothing -> case Map.lookup (FnName name) fns of
      Just (WI.SomeSymFn fn) ->
        case WI.fnArgTypes fn of
          Ctx.Empty -> do
            result <- WI.applySymFn sym fn Ctx.Empty
            return (Just (SomeExpr result))
          _ -> return Nothing
      Nothing -> parseAtomLiteral sym name

parseAtomLiteral ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  Text ->
  IO (Maybe (SomeExpr sym))
parseAtomLiteral sym name = do
  let s = Text.unpack name
  if "#b" `isPrefixOf` s then parseBinaryBV sym s
  else if "#x" `isPrefixOf` s then parseHexBV sym s
  else do
    intResult <- parseIntegerLiteral sym s
    case intResult of
      Just val -> return (Just val)
      Nothing -> parseRealLiteral sym s

parseBinaryBV ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  String ->
  IO (Maybe (SomeExpr sym))
parseBinaryBV sym s = do
  let bits = drop 2 s
  if not (null bits) && all (`elem` ("01" :: String)) bits then do
    let val = bitsToInteger bits
    let width = fromIntegral @Int @Natural (length bits)
    case NatRepr.mkNatRepr width of
      Some w -> case NatRepr.testLeq (NatRepr.knownNat @1) w of
        Just NatRepr.LeqProof -> do
          bv <- WI.bvLit sym w (BV.mkBV w val)
          return (Just (SomeExpr bv))
        Nothing -> return Nothing
  else return Nothing

parseHexBV ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  String ->
  IO (Maybe (SomeExpr sym))
parseHexBV sym s = do
  let hex = drop 2 s
  if not (null hex) && all (`elem` ("0123456789abcdefABCDEF" :: String)) hex then do
    let val = hexToInteger hex
    let width = fromIntegral @Int @Natural (length hex * 4)
    case NatRepr.mkNatRepr width of
      Some w -> case NatRepr.testLeq (NatRepr.knownNat @1) w of
        Just NatRepr.LeqProof -> do
          bv <- WI.bvLit sym w (BV.mkBV w val)
          return (Just (SomeExpr bv))
        Nothing -> return Nothing
  else return Nothing

parseIntegerLiteral ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  String ->
  IO (Maybe (SomeExpr sym))
parseIntegerLiteral sym s = do
  case reads s of
    [(n, "")] -> do
      intVal <- WI.intLit sym n
      return (Just (SomeExpr intVal))
    _ -> return Nothing

parseRealLiteral ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  String ->
  IO (Maybe (SomeExpr sym))
parseRealLiteral sym s = do
  case reads s of
    [(n, "")] | '.' `elem` s -> do
      realVal <- WI.realLit sym (toRational (n :: Double))
      return (Just (SomeExpr realVal))
    _ -> return Nothing

-- | Parse an expression s-expression
parseExpr ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  Map VarName (SomeExpr sym) ->
  Map FnName (WI.SomeSymFn sym) ->
  SExp.SExp ->
  IO (SomeExpr sym)
parseExpr sym vars fns = \case
  [sexp|true|] -> return $ SomeExpr (WI.truePred sym)
  [sexp|false|] -> return $ SomeExpr (WI.falsePred sym)

  SExp.SAtom atom -> do
    result <- parseAtom sym vars fns atom
    case result of
      Just val -> return val
      Nothing -> Pretty.userErr $ "unknown atom:" <+> PP.pretty (Pretty.ppSExp (SExp.SAtom atom))

  [sexp|(#_ bv#valStr $size)|]
    | [(val, "")] <- reads @Integer valStr
    , Some w <- NatRepr.mkNatRepr (fromIntegral size)
    , Just NatRepr.LeqProof <- NatRepr.testLeq (NatRepr.knownNat @1) w
    -> do bv <- WI.bvLit sym w (BV.mkBV w val)
          pure (SomeExpr bv)

  [sexp|(#fnNameSexp ...argSexps)|]
    | SExp.SAtom fnName <- fnNameSexp
    , Just fnDef <- Map.lookup (FnName fnName) fns ->
        applyFunction sym vars fns fnDef argSexps

  [sexp|(= #e1 #e2)|] -> do
    SomeExpr e1' <- parseExpr sym vars fns e1
    SomeExpr e2' <- parseExpr sym vars fns e2
    case WBT.testEquality (WI.exprType e1') (WI.exprType e2') of
      Just WBT.Refl -> SomeExpr <$> WI.isEq sym e1' e2'
      Nothing -> case (WI.exprType e1', WI.exprType e2') of
        (WBT.BaseRealRepr, WBT.BaseIntegerRepr) -> do
          r2 <- WI.integerToReal sym e2'
          SomeExpr <$> WI.isEq sym e1' r2
        (WBT.BaseIntegerRepr, WBT.BaseRealRepr) -> do
          r1 <- WI.integerToReal sym e1'
          SomeExpr <$> WI.isEq sym r1 e2'
        _ -> Pretty.userErr $
          "type mismatch in =:" <+> PP.viaShow (WI.exprType e1') <+> "vs" <+> PP.viaShow (WI.exprType e2')

  [sexp|(distinct #e1 #e2)|] -> do
    SomeExpr e1' <- parseExpr sym vars fns e1
    SomeExpr e2' <- parseExpr sym vars fns e2
    case WBT.testEquality (WI.exprType e1') (WI.exprType e2') of
      Just WBT.Refl -> do
        eq <- WI.isEq sym e1' e2'
        SomeExpr <$> WI.notPred sym eq
      Nothing -> case (WI.exprType e1', WI.exprType e2') of
        (WBT.BaseRealRepr, WBT.BaseIntegerRepr) -> do
          r2 <- WI.integerToReal sym e2'
          eq <- WI.isEq sym e1' r2
          SomeExpr <$> WI.notPred sym eq
        (WBT.BaseIntegerRepr, WBT.BaseRealRepr) -> do
          r1 <- WI.integerToReal sym e1'
          eq <- WI.isEq sym r1 e2'
          SomeExpr <$> WI.notPred sym eq
        _ -> Pretty.userErr "type mismatch in distinct"

  [sexp|(not #e)|] -> do
    SomeExpr e' <- parseExpr sym vars fns e
    case WBT.testEquality (WI.exprType e') WBT.BaseBoolRepr of
      Just WBT.Refl -> SomeExpr <$> WI.notPred sym e'
      Nothing -> Pretty.userErr "not requires Bool"

  [sexp|(and ...args)|] -> do
    preds <- mapM (parseBoolExpr sym vars fns) args
    SomeExpr <$> Monad.foldM (WI.andPred sym) (WI.truePred sym) preds

  [sexp|(or ...args)|] -> do
    preds <- mapM (parseBoolExpr sym vars fns) args
    SomeExpr <$> Monad.foldM (WI.orPred sym) (WI.falsePred sym) preds

  [sexp|(=> #e1 #e2)|] -> do
    p1 <- parseBoolExpr sym vars fns e1
    p2 <- parseBoolExpr sym vars fns e2
    SomeExpr <$> WI.impliesPred sym p1 p2

  [sexp|(ite #condExpr #eThen #eElse)|] -> do
    cond <- parseBoolExpr sym vars fns condExpr
    SomeExpr eThen' <- parseExpr sym vars fns eThen
    SomeExpr eElse' <- parseExpr sym vars fns eElse
    case WBT.testEquality (WI.exprType eThen') (WI.exprType eElse') of
      Just WBT.Refl -> SomeExpr <$> WI.baseTypeIte sym cond eThen' eElse'
      Nothing -> case (WI.exprType eThen', WI.exprType eElse') of
        (WBT.BaseRealRepr, WBT.BaseIntegerRepr) -> do
          rElse <- WI.integerToReal sym eElse'
          SomeExpr <$> WI.baseTypeIte sym cond eThen' rElse
        (WBT.BaseIntegerRepr, WBT.BaseRealRepr) -> do
          rThen <- WI.integerToReal sym eThen'
          SomeExpr <$> WI.baseTypeIte sym cond rThen eElse'
        _ -> Pretty.userErr $
          "ite requires same types for then and else:" <+> PP.viaShow (WI.exprType eThen') <+> "vs" <+> PP.viaShow (WI.exprType eElse')

  [sexp|((#_ extract $high $low) #bvExpr)|]
    | let resultWidth = high - low + 1
    , resultWidth > 0
    , let lowNat = fromIntegral @Integer @Natural low
    , let resultNat = fromIntegral @Integer @Natural resultWidth
    , Some lowIdx <- NatRepr.mkNatRepr lowNat
    , Some resultW <- NatRepr.mkNatRepr resultNat
    , Just NatRepr.LeqProof <- NatRepr.testLeq (NatRepr.knownNat @1) resultW
    -> do
      SomeExpr bv <- parseExpr sym vars fns bvExpr
      case WI.exprType bv of
        WBT.BaseBVRepr w ->
          case NatRepr.testLeq (lowIdx `NatRepr.addNat` resultW) w of
            Just NatRepr.LeqProof -> do
              selected <- WI.bvSelect sym lowIdx resultW bv
              return (SomeExpr selected)
            _ -> Pretty.userErr "extract indices out of range"
        _ -> Pretty.userErr "extract requires a bitvector argument"

  [sexp|((#_ zero_extend $n) #bvExpr)|]
    | let extendNat = fromIntegral @Integer @Natural n
    , Some extendW <- NatRepr.mkNatRepr extendNat
    , Just oneLeqExtend@NatRepr.LeqProof <- NatRepr.testLeq (NatRepr.knownNat @1) extendW
    -> do
      SomeExpr bv <- parseExpr sym vars fns bvExpr
      case WI.exprType bv of
        WBT.BaseBVRepr w -> do
          let resultW = w `NatRepr.addNat` extendW
          let wLeqW = NatRepr.leqRefl w
          NatRepr.LeqProof <- return (NatRepr.leqAdd2 wLeqW oneLeqExtend)
          extended <- WI.bvZext sym resultW bv
          return (SomeExpr extended)
        _ -> Pretty.userErr "zero_extend requires a bitvector argument"

  [sexp|((#_ sign_extend $n) #bvExpr)|]
    | let extendNat = fromIntegral @Integer @Natural n
    , Some extendW <- NatRepr.mkNatRepr extendNat
    , Just oneLeqExtend@NatRepr.LeqProof <- NatRepr.testLeq (NatRepr.knownNat @1) extendW
    -> do
      SomeExpr bv <- parseExpr sym vars fns bvExpr
      case WI.exprType bv of
        WBT.BaseBVRepr w -> do
          let resultW = w `NatRepr.addNat` extendW
          let wLeqW = NatRepr.leqRefl w
          NatRepr.LeqProof <- return (NatRepr.leqAdd2 wLeqW oneLeqExtend)
          extended <- WI.bvSext sym resultW bv
          return (SomeExpr extended)
        _ -> Pretty.userErr "sign_extend requires a bitvector argument"

  [sexp|(concat #e1 #e2)|] -> do
    SomeExpr bv1 <- parseExpr sym vars fns e1
    SomeExpr bv2 <- parseExpr sym vars fns e2
    case (WI.exprType bv1, WI.exprType bv2) of
      (WBT.BaseBVRepr _w1, WBT.BaseBVRepr _w2) ->
        SomeExpr <$> WI.bvConcat sym bv1 bv2
      _ -> Pretty.userErr "concat requires bitvector arguments"

  [sexp|(bvnot #e)|] -> do
    SomeExpr bv <- parseExpr sym vars fns e
    case WI.exprType bv of
      WBT.BaseBVRepr _ -> SomeExpr <$> WI.bvNotBits sym bv
      _ -> Pretty.userErr "bvnot requires a bitvector argument"

  [sexp|(bvneg #e)|] -> do
    SomeExpr bv <- parseExpr sym vars fns e
    case WI.exprType bv of
      WBT.BaseBVRepr _ -> SomeExpr <$> WI.bvNeg sym bv
      _ -> Pretty.userErr "bvneg requires a bitvector argument"

  [sexp|(bv#opName #e1 #e2)|] -> do
    SomeExpr e1' <- parseExpr sym vars fns e1
    SomeExpr e2' <- parseExpr sym vars fns e2
    case (WI.exprType e1', WI.exprType e2') of
      (WBT.BaseBVRepr w1, WBT.BaseBVRepr w2)
        | Just WBT.Refl <- WBT.testEquality w1 w2 ->
            parseBVOp sym opName e1' e2'
      _ -> Pretty.userErr $ PP.pretty ("bv" ++ opName ++ " requires equal-width bitvector arguments")

  [sexp|(let #bindingsList #body)|] -> do
    bindings <- parseLetBindings sym vars bindingsList
    let extendedVars = Map.union (Map.fromList bindings) vars
    parseExpr sym extendedVars fns body

  [sexp|(/ #e1 #e2)|] -> do
    SomeExpr e1' <- parseExpr sym vars fns e1
    SomeExpr e2' <- parseExpr sym vars fns e2
    case (WI.exprType e1', WI.exprType e2') of
      (WBT.BaseIntegerRepr, WBT.BaseIntegerRepr) -> do
        case (WI.asInteger e1', WI.asInteger e2') of
          (Just n, Just d) | d /= 0 -> do
            realVal <- WI.realLit sym (n % d)
            return (SomeExpr realVal)
          _ -> do
            r1 <- WI.integerToReal sym e1'
            r2 <- WI.integerToReal sym e2'
            SomeExpr <$> WI.realDiv sym r1 r2
      (WBT.BaseRealRepr, WBT.BaseRealRepr) ->
        SomeExpr <$> WI.realDiv sym e1' e2'
      _ -> Pretty.userErr "/ requires numeric arguments"

  [sexp|(+ ...args)|] -> do
    case args of
      [] -> SomeExpr <$> WI.intLit sym 0
      [e1] -> parseExpr sym vars fns e1
      _ -> do
        exprs <- forM args $ \arg -> parseExpr sym vars fns arg
        case exprs of
          [] -> SomeExpr <$> WI.intLit sym 0
          (SomeExpr _ : _) ->
            -- Check if any argument is Real
            let hasReal = any (\(SomeExpr e) -> case WI.exprType e of
                  WBT.BaseRealRepr -> True
                  _ -> False) exprs
            in if hasReal then do
              -- Convert all to Real and add
              allReals <- forM exprs $ \(SomeExpr e) ->
                case WI.exprType e of
                  WBT.BaseRealRepr -> return e
                  WBT.BaseIntegerRepr -> WI.integerToReal sym e
                  _ -> Pretty.userErr "+ requires integer or real arguments"
              zero <- WI.realLit sym 0
              result <- Monad.foldM (WI.realAdd sym) zero allReals
              return (SomeExpr result)
            else do
              -- All integers
              allInts <- forM exprs $ \(SomeExpr e) ->
                case WI.exprType e of
                  WBT.BaseIntegerRepr -> return e
                  _ -> Pretty.userErr "+ requires integer or real arguments"
              zero <- WI.intLit sym 0
              result <- Monad.foldM (WI.intAdd sym) zero allInts
              return (SomeExpr result)

  [sexp|(- #e1 ...rest)|] -> do
    SomeExpr e1' <- parseExpr sym vars fns e1
    case rest of
      [] -> do
        case WI.exprType e1' of
          WBT.BaseIntegerRepr -> SomeExpr <$> WI.intNeg sym e1'
          WBT.BaseRealRepr -> SomeExpr <$> WI.realNeg sym e1'
          _ -> Pretty.userErr "unary - requires integer or real argument"
      [e2] -> do
        SomeExpr e2' <- parseExpr sym vars fns e2
        case (WI.exprType e1', WI.exprType e2') of
          (WBT.BaseIntegerRepr, WBT.BaseIntegerRepr) ->
            SomeExpr <$> WI.intSub sym e1' e2'
          (WBT.BaseRealRepr, WBT.BaseRealRepr) ->
            SomeExpr <$> WI.realSub sym e1' e2'
          (WBT.BaseRealRepr, WBT.BaseIntegerRepr) -> do
            r2 <- WI.integerToReal sym e2'
            SomeExpr <$> WI.realSub sym e1' r2
          (WBT.BaseIntegerRepr, WBT.BaseRealRepr) -> do
            r1 <- WI.integerToReal sym e1'
            SomeExpr <$> WI.realSub sym r1 e2'
          _ -> Pretty.userErr "- requires integer or real arguments"
      _ -> Pretty.userErr "- expects 1 or 2 arguments"

  [sexp|(* ...args)|] -> do
    case args of
      [] -> SomeExpr <$> WI.intLit sym 1
      [e1] -> parseExpr sym vars fns e1
      _ -> do
        exprs <- forM args $ \arg -> parseExpr sym vars fns arg
        case exprs of
          [] -> SomeExpr <$> WI.intLit sym 1
          (SomeExpr _ : _) ->
            let hasReal = any (\(SomeExpr e) -> case WI.exprType e of
                  WBT.BaseRealRepr -> True
                  _ -> False) exprs
            in if hasReal then do
              allReals <- forM exprs $ \(SomeExpr e) ->
                case WI.exprType e of
                  WBT.BaseRealRepr -> return e
                  WBT.BaseIntegerRepr -> WI.integerToReal sym e
                  _ -> Pretty.userErr "* requires integer or real arguments"
              one <- WI.realLit sym 1
              result <- Monad.foldM (WI.realMul sym) one allReals
              return (SomeExpr result)
            else do
              allInts <- forM exprs $ \(SomeExpr e) ->
                case WI.exprType e of
                  WBT.BaseIntegerRepr -> return e
                  _ -> Pretty.userErr "* requires integer or real arguments"
              one <- WI.intLit sym 1
              result <- Monad.foldM (WI.intMul sym) one allInts
              return (SomeExpr result)

  [sexp|(div #e1 #e2)|] -> do
    SomeExpr e1' <- parseExpr sym vars fns e1
    SomeExpr e2' <- parseExpr sym vars fns e2
    case (WI.exprType e1', WI.exprType e2') of
      (WBT.BaseIntegerRepr, WBT.BaseIntegerRepr) ->
        SomeExpr <$> WI.intDiv sym e1' e2'
      _ -> Pretty.userErr "div requires integer arguments"

  [sexp|(mod #e1 #e2)|] -> do
    SomeExpr e1' <- parseExpr sym vars fns e1
    SomeExpr e2' <- parseExpr sym vars fns e2
    case (WI.exprType e1', WI.exprType e2') of
      (WBT.BaseIntegerRepr, WBT.BaseIntegerRepr) ->
        SomeExpr <$> WI.intMod sym e1' e2'
      _ -> Pretty.userErr "mod requires integer arguments"

  [sexp|(abs #e)|] -> do
    SomeExpr e' <- parseExpr sym vars fns e
    case WI.exprType e' of
      WBT.BaseIntegerRepr -> SomeExpr <$> WI.intAbs sym e'
      WBT.BaseRealRepr -> SomeExpr <$> WI.realAbs sym e'
      _ -> Pretty.userErr "abs requires integer or real argument"

  [sexp|(< #e1 #e2)|] -> do
    SomeExpr e1' <- parseExpr sym vars fns e1
    SomeExpr e2' <- parseExpr sym vars fns e2
    case (WI.exprType e1', WI.exprType e2') of
      (WBT.BaseIntegerRepr, WBT.BaseIntegerRepr) ->
        SomeExpr <$> WI.intLt sym e1' e2'
      (WBT.BaseRealRepr, WBT.BaseRealRepr) ->
        SomeExpr <$> WI.realLt sym e1' e2'
      (WBT.BaseRealRepr, WBT.BaseIntegerRepr) -> do
        r2 <- WI.integerToReal sym e2'
        SomeExpr <$> WI.realLt sym e1' r2
      (WBT.BaseIntegerRepr, WBT.BaseRealRepr) -> do
        r1 <- WI.integerToReal sym e1'
        SomeExpr <$> WI.realLt sym r1 e2'
      _ -> Pretty.userErr "< requires integer or real arguments"

  [sexp|(<= #e1 #e2)|] -> do
    SomeExpr e1' <- parseExpr sym vars fns e1
    SomeExpr e2' <- parseExpr sym vars fns e2
    case (WI.exprType e1', WI.exprType e2') of
      (WBT.BaseIntegerRepr, WBT.BaseIntegerRepr) ->
        SomeExpr <$> WI.intLe sym e1' e2'
      (WBT.BaseRealRepr, WBT.BaseRealRepr) ->
        SomeExpr <$> WI.realLe sym e1' e2'
      (WBT.BaseRealRepr, WBT.BaseIntegerRepr) -> do
        r2 <- WI.integerToReal sym e2'
        SomeExpr <$> WI.realLe sym e1' r2
      (WBT.BaseIntegerRepr, WBT.BaseRealRepr) -> do
        r1 <- WI.integerToReal sym e1'
        SomeExpr <$> WI.realLe sym r1 e2'
      _ -> Pretty.userErr "<= requires integer or real arguments"

  [sexp|(> #e1 #e2)|] -> do
    SomeExpr e1' <- parseExpr sym vars fns e1
    SomeExpr e2' <- parseExpr sym vars fns e2
    case (WI.exprType e1', WI.exprType e2') of
      (WBT.BaseIntegerRepr, WBT.BaseIntegerRepr) ->
        SomeExpr <$> WI.intLt sym e2' e1'
      (WBT.BaseRealRepr, WBT.BaseRealRepr) ->
        SomeExpr <$> WI.realLt sym e2' e1'
      (WBT.BaseRealRepr, WBT.BaseIntegerRepr) -> do
        r2 <- WI.integerToReal sym e2'
        SomeExpr <$> WI.realLt sym r2 e1'
      (WBT.BaseIntegerRepr, WBT.BaseRealRepr) -> do
        r1 <- WI.integerToReal sym e1'
        SomeExpr <$> WI.realLt sym e2' r1
      _ -> Pretty.userErr "> requires integer or real arguments"

  [sexp|(>= #e1 #e2)|] -> do
    SomeExpr e1' <- parseExpr sym vars fns e1
    SomeExpr e2' <- parseExpr sym vars fns e2
    case (WI.exprType e1', WI.exprType e2') of
      (WBT.BaseIntegerRepr, WBT.BaseIntegerRepr) ->
        SomeExpr <$> WI.intLe sym e2' e1'
      (WBT.BaseRealRepr, WBT.BaseRealRepr) ->
        SomeExpr <$> WI.realLe sym e2' e1'
      (WBT.BaseRealRepr, WBT.BaseIntegerRepr) -> do
        r2 <- WI.integerToReal sym e2'
        SomeExpr <$> WI.realLe sym r2 e1'
      (WBT.BaseIntegerRepr, WBT.BaseRealRepr) -> do
        r1 <- WI.integerToReal sym e1'
        SomeExpr <$> WI.realLe sym e2' r1
      _ -> Pretty.userErr ">= requires integer or real arguments"

  other -> Pretty.unsupported $ "expression:" <+> PP.pretty (Pretty.ppSExp other)

-- | Parse an expression that must be Bool
parseBoolExpr ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  Map VarName (SomeExpr sym) ->
  Map FnName (WI.SomeSymFn sym) ->
  SExp.SExp ->
  IO (WI.Pred sym)
parseBoolExpr sym vars fns sexp' = do
  SomeExpr e <- parseExpr sym vars fns sexp'
  case WBT.testEquality (WI.exprType e) WBT.BaseBoolRepr of
    Just WBT.Refl -> return e
    Nothing -> Pretty.userErr $ "expected Bool, got" <+> PP.viaShow (WI.exprType e)

-- | Parse a bitvector operation
parseBVOp ::
  (1 <= w, WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  String ->
  WI.SymBV sym w ->
  WI.SymBV sym w ->
  IO (SomeExpr sym)
parseBVOp sym op e1 e2 = case op of
  "add" -> SomeExpr <$> WI.bvAdd sym e1 e2
  "sub" -> SomeExpr <$> WI.bvSub sym e1 e2
  "mul" -> SomeExpr <$> WI.bvMul sym e1 e2
  "udiv" -> SomeExpr <$> WI.bvUdiv sym e1 e2
  "sdiv" -> SomeExpr <$> WI.bvSdiv sym e1 e2
  "urem" -> SomeExpr <$> WI.bvUrem sym e1 e2
  "srem" -> SomeExpr <$> WI.bvSrem sym e1 e2
  "and" -> SomeExpr <$> WI.bvAndBits sym e1 e2
  "or" -> SomeExpr <$> WI.bvOrBits sym e1 e2
  "xor" -> SomeExpr <$> WI.bvXorBits sym e1 e2
  "shl" -> SomeExpr <$> WI.bvShl sym e1 e2
  "lshr" -> SomeExpr <$> WI.bvLshr sym e1 e2
  "ashr" -> SomeExpr <$> WI.bvAshr sym e1 e2
  "ult" -> SomeExpr <$> WI.bvUlt sym e1 e2
  "slt" -> SomeExpr <$> WI.bvSlt sym e1 e2
  "ule" -> SomeExpr <$> WI.bvUle sym e1 e2
  "sle" -> SomeExpr <$> WI.bvSle sym e1 e2
  "ugt" -> SomeExpr <$> WI.bvUgt sym e1 e2
  "sgt" -> SomeExpr <$> WI.bvSgt sym e1 e2
  "uge" -> SomeExpr <$> WI.bvUge sym e1 e2
  "sge" -> SomeExpr <$> WI.bvSge sym e1 e2
  _ -> Pretty.unsupported $ PP.pretty ("bitvector operation: bv" ++ op)

-- | Convert a binary string to an integer (e.g., "101" -> 5)
bitsToInteger :: String -> Integer
bitsToInteger = foldl (\acc c -> acc * 2 + if c == '1' then 1 else 0) 0

-- | Convert a hexadecimal string to an integer
hexToInteger :: String -> Integer
hexToInteger s = read ("0x" ++ s)


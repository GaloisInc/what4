{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module W4SMT2.Parser
  ( parseSExps
  , parseType
  , parseExpr
  , parseBoolExpr
  ) where

import Control.Applicative ((<|>))
import Control.Monad (forM)
import Control.Monad qualified as Monad
import Data.Attoparsec.Text qualified as A
import Data.BitVector.Sized qualified as BV
import Data.List (isPrefixOf)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Numeric.Natural (Natural)
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

    -- Skip whitespace and comments (lines starting with ;)
    skipSpaceAndComments :: A.Parser ()
    skipSpaceAndComments = A.skipWhile (\c -> c `elem` (" \t\n\r" :: String)) <* A.skipMany comment
      where
        comment = A.char ';' *> A.skipWhile (/= '\n') *> (A.char '\n' >> pure () <|> pure ())

    -- Simple string literal parser
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
-- Takes a list of (var expr) pairs and returns (Text, Some (WI.SymExpr sym)) pairs
-- Strips leading ?, _, or $ from variable names (if present)
parseLetBindings ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  Map Text (Some (WI.SymExpr sym)) ->
  SExp.SExp ->
  IO [(Text, Some (WI.SymExpr sym))]
parseLetBindings sym vars (SExp.SApp bindingPairs) = do
  forM bindingPairs $ \case
    [sexp|(#varName #exprSExp)|]
      | SExp.SAtom name <- varName -> do
          Some expr <- parseExpr sym vars exprSExp
          return (name, Some expr)
    other -> Pretty.userErr $ "invalid let binding:" <+> PP.pretty (Pretty.ppSExp other)
parseLetBindings _ _ other =
  Pretty.userErr $ "let bindings must be a list:" <+> PP.pretty (Pretty.ppSExp other)

parseAtom ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  Map Text (Some (WI.SymExpr sym)) ->
  Text ->
  IO (Maybe (Some (WI.SymExpr sym)))
parseAtom sym vars name = do
  case Map.lookup name vars of
    Just var -> return (Just var)
    Nothing -> parseAtomLiteral sym name

parseAtomLiteral ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  Text ->
  IO (Maybe (Some (WI.SymExpr sym)))
parseAtomLiteral sym name = do
  let s = Text.unpack name
  if "#b" `isPrefixOf` s then parseBinaryBV sym s
  else if "#x" `isPrefixOf` s then parseHexBV sym s
  else parseIntegerLiteral sym s

parseBinaryBV ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  String ->
  IO (Maybe (Some (WI.SymExpr sym)))
parseBinaryBV sym s = do
  let bits = drop 2 s
  if not (null bits) && all (`elem` ("01" :: String)) bits then do
    let val = bitsToInteger bits
    let width = fromIntegral @Int @Natural (length bits)
    case NatRepr.mkNatRepr width of
      Some w -> case NatRepr.testLeq (NatRepr.knownNat @1) w of
        Just NatRepr.LeqProof -> do
          bv <- WI.bvLit sym w (BV.mkBV w val)
          return (Just (Some bv))
        Nothing -> return Nothing
  else return Nothing

parseHexBV ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  String ->
  IO (Maybe (Some (WI.SymExpr sym)))
parseHexBV sym s = do
  let hex = drop 2 s
  if not (null hex) && all (`elem` ("0123456789abcdefABCDEF" :: String)) hex then do
    let val = hexToInteger hex
    let width = fromIntegral @Int @Natural (length hex * 4)
    case NatRepr.mkNatRepr width of
      Some w -> case NatRepr.testLeq (NatRepr.knownNat @1) w of
        Just NatRepr.LeqProof -> do
          bv <- WI.bvLit sym w (BV.mkBV w val)
          return (Just (Some bv))
        Nothing -> return Nothing
  else return Nothing

parseIntegerLiteral ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  String ->
  IO (Maybe (Some (WI.SymExpr sym)))
parseIntegerLiteral sym s = do
  case reads s of
    [(n, "")] -> do
      intVal <- WI.intLit sym n
      return (Just (Some intVal))
    _ -> return Nothing

-- | Parse an expression s-expression
parseExpr ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  Map Text (Some (WI.SymExpr sym)) ->
  SExp.SExp ->
  IO (Some (WI.SymExpr sym))
parseExpr sym vars = \case
  [sexp|true|] -> return $ Some (WI.truePred sym)
  [sexp|false|] -> return $ Some (WI.falsePred sym)

  SExp.SAtom atom -> do
    result <- parseAtom sym vars atom
    case result of
      Just val -> return val
      Nothing -> Pretty.userErr $ "unknown atom:" <+> PP.pretty (Pretty.ppSExp (SExp.SAtom atom))

  [sexp|(#_ bv#valStr $size)|]
    | [(val, "")] <- reads @Integer valStr
    , Some w <- NatRepr.mkNatRepr (fromIntegral size)
    , Just NatRepr.LeqProof <- NatRepr.testLeq (NatRepr.knownNat @1) w
    -> do bv <- WI.bvLit sym w (BV.mkBV w val)
          pure (Some bv)

  [sexp|(= #e1 #e2)|] -> do
    Some e1' <- parseExpr sym vars e1
    Some e2' <- parseExpr sym vars e2
    case WBT.testEquality (WI.exprType e1') (WI.exprType e2') of
      Just WBT.Refl -> Some <$> WI.isEq sym e1' e2'
      Nothing -> Pretty.userErr $
        "type mismatch in =:" <+> PP.viaShow (WI.exprType e1') <+> "vs" <+> PP.viaShow (WI.exprType e2')

  [sexp|(distinct #e1 #e2)|] -> do
    Some e1' <- parseExpr sym vars e1
    Some e2' <- parseExpr sym vars e2
    case WBT.testEquality (WI.exprType e1') (WI.exprType e2') of
      Just WBT.Refl -> do
        eq <- WI.isEq sym e1' e2'
        Some <$> WI.notPred sym eq
      Nothing -> Pretty.userErr "type mismatch in distinct"

  [sexp|(not #e)|] -> do
    Some e' <- parseExpr sym vars e
    case WBT.testEquality (WI.exprType e') WBT.BaseBoolRepr of
      Just WBT.Refl -> Some <$> WI.notPred sym e'
      Nothing -> Pretty.userErr "not requires Bool"

  [sexp|(and ...args)|] -> do
    preds <- mapM (parseBoolExpr sym vars) args
    Some <$> Monad.foldM (WI.andPred sym) (WI.truePred sym) preds

  [sexp|(or ...args)|] -> do
    preds <- mapM (parseBoolExpr sym vars) args
    Some <$> Monad.foldM (WI.orPred sym) (WI.falsePred sym) preds

  [sexp|(=> #e1 #e2)|] -> do
    p1 <- parseBoolExpr sym vars e1
    p2 <- parseBoolExpr sym vars e2
    Some <$> WI.impliesPred sym p1 p2

  [sexp|(ite #condExpr #eThen #eElse)|] -> do
    cond <- parseBoolExpr sym vars condExpr
    Some eThen' <- parseExpr sym vars eThen
    Some eElse' <- parseExpr sym vars eElse
    case WBT.testEquality (WI.exprType eThen') (WI.exprType eElse') of
      Just WBT.Refl -> Some <$> WI.baseTypeIte sym cond eThen' eElse'
      Nothing -> Pretty.userErr $
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
      Some bv <- parseExpr sym vars bvExpr
      case WI.exprType bv of
        WBT.BaseBVRepr w ->
          case NatRepr.testLeq (lowIdx `NatRepr.addNat` resultW) w of
            Just NatRepr.LeqProof -> do
              selected <- WI.bvSelect sym lowIdx resultW bv
              return (Some selected)
            _ -> Pretty.userErr "extract indices out of range"
        _ -> Pretty.userErr "extract requires a bitvector argument"

  [sexp|(concat #e1 #e2)|] -> do
    Some bv1 <- parseExpr sym vars e1
    Some bv2 <- parseExpr sym vars e2
    case (WI.exprType bv1, WI.exprType bv2) of
      (WBT.BaseBVRepr _w1, WBT.BaseBVRepr _w2) ->
        Some <$> WI.bvConcat sym bv1 bv2
      _ -> Pretty.userErr "concat requires bitvector arguments"

  [sexp|(bvnot #e)|] -> do
    Some bv <- parseExpr sym vars e
    case WI.exprType bv of
      WBT.BaseBVRepr _ -> Some <$> WI.bvNotBits sym bv
      _ -> Pretty.userErr "bvnot requires a bitvector argument"

  [sexp|(bvneg #e)|] -> do
    Some bv <- parseExpr sym vars e
    case WI.exprType bv of
      WBT.BaseBVRepr _ -> Some <$> WI.bvNeg sym bv
      _ -> Pretty.userErr "bvneg requires a bitvector argument"

  [sexp|(bv#opName #e1 #e2)|] -> do
    Some e1' <- parseExpr sym vars e1
    Some e2' <- parseExpr sym vars e2
    case (WI.exprType e1', WI.exprType e2') of
      (WBT.BaseBVRepr w1, WBT.BaseBVRepr w2)
        | Just WBT.Refl <- WBT.testEquality w1 w2 ->
            parseBVOp sym opName e1' e2'
      _ -> Pretty.userErr $ PP.pretty ("bv" ++ opName ++ " requires equal-width bitvector arguments")

  [sexp|(let #bindingsList #body)|] -> do
    bindings <- parseLetBindings sym vars bindingsList
    let extendedVars = Map.union (Map.fromList bindings) vars
    parseExpr sym extendedVars body

  other -> Pretty.unsupported $ "expression:" <+> PP.pretty (Pretty.ppSExp other)

-- | Parse an expression that must be Bool
parseBoolExpr ::
  (WI.IsSymExprBuilder sym, ?logStderr :: Text -> IO ()) =>
  sym ->
  Map Text (Some (WI.SymExpr sym)) ->
  SExp.SExp ->
  IO (WI.Pred sym)
parseBoolExpr sym vars sexp' = do
  Some e <- parseExpr sym vars sexp'
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
  IO (Some (WI.SymExpr sym))
parseBVOp sym op e1 e2 = case op of
  "add" -> Some <$> WI.bvAdd sym e1 e2
  "sub" -> Some <$> WI.bvSub sym e1 e2
  "mul" -> Some <$> WI.bvMul sym e1 e2
  "udiv" -> Some <$> WI.bvUdiv sym e1 e2
  "sdiv" -> Some <$> WI.bvSdiv sym e1 e2
  "urem" -> Some <$> WI.bvUrem sym e1 e2
  "srem" -> Some <$> WI.bvSrem sym e1 e2
  "and" -> Some <$> WI.bvAndBits sym e1 e2
  "or" -> Some <$> WI.bvOrBits sym e1 e2
  "xor" -> Some <$> WI.bvXorBits sym e1 e2
  "shl" -> Some <$> WI.bvShl sym e1 e2
  "lshr" -> Some <$> WI.bvLshr sym e1 e2
  "ashr" -> Some <$> WI.bvAshr sym e1 e2
  "ult" -> Some <$> WI.bvUlt sym e1 e2
  "slt" -> Some <$> WI.bvSlt sym e1 e2
  "ule" -> Some <$> WI.bvUle sym e1 e2
  "sle" -> Some <$> WI.bvSle sym e1 e2
  "ugt" -> Some <$> WI.bvUgt sym e1 e2
  "sgt" -> Some <$> WI.bvSgt sym e1 e2
  "uge" -> Some <$> WI.bvUge sym e1 e2
  "sge" -> Some <$> WI.bvSge sym e1 e2
  _ -> Pretty.unsupported $ PP.pretty ("bitvector operation: bv" ++ op)

-- | Convert a binary string to an integer (e.g., "101" -> 5)
bitsToInteger :: String -> Integer
bitsToInteger = foldl (\acc c -> acc * 2 + if c == '1' then 1 else 0) 0

-- | Convert a hexadecimal string to an integer
hexToInteger :: String -> Integer
hexToInteger s = read ("0x" ++ s)


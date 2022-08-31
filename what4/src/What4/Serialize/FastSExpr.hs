{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
-- | This module implements a specialized s-expression parser
--
-- The parser in s-cargot is very general, but that also makes it a bit
-- inefficient.  This module implements a drop-in replacement parser for the one
-- in What4.Serialize.Parser using megaparsec.  It is completely specialized to
-- the types in this library.
module What4.Serialize.FastSExpr (
  parseSExpr
  ) where

import           Control.Applicative
import qualified Control.Monad.Fail as MF
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import           Data.Ratio ( (%) )
import qualified Data.SCargot.Repr.WellFormed as SC
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified LibBF as BF
import           Numeric.Natural ( Natural )
import qualified Text.Megaparsec as TM
import qualified Text.Megaparsec.Char as TMC
import qualified Text.Megaparsec.Char.Lexer as TMCL
import qualified What4.BaseTypes as WT
import qualified What4.Serialize.SETokens as WST

-- | Parse 'T.Text' into the well-formed s-expression type from s-cargot.
parseSExpr :: T.Text -> Either String (SC.WellFormedSExpr WST.Atom)
parseSExpr t =
  case TM.runParser (ws >> parse) "<input>" t of
    Left errBundle -> Left (TM.errorBundlePretty errBundle)
    Right a -> Right a

data What4ParseError = ErrorParsingHexFloat String
                     | InvalidExponentOrSignificandSize Natural Natural
  deriving (Show, Eq, Ord)

instance TM.ShowErrorComponent What4ParseError where
  showErrorComponent e =
    case e of
      ErrorParsingHexFloat hf -> "Error parsing hex float literal: " ++ hf
      InvalidExponentOrSignificandSize ex s ->
        concat [ "Invalid exponent or significand size: exponent size = "
               , show ex
               , ", significand size = "
               , show s
               ]

type Parser a = TM.Parsec What4ParseError T.Text a

parse :: Parser (SC.WellFormedSExpr WST.Atom)
parse = parseList <|> (SC.WFSAtom <$> lexeme parseAtom)

parseList :: Parser (SC.WellFormedSExpr WST.Atom)
parseList = do
  _ <- lexeme (TMC.char '(')
  items <- TM.many parse
  _ <- lexeme (TMC.char ')')
  return (SC.WFSList items)

parseId :: Parser T.Text
parseId = T.pack <$> ((:) <$> first <*> TM.many rest)
  where
    w4symbol c = c == '@'
               || c == '+'
               || c == '-'
               || c == '='
               || c == '<'
               || c == '>'
               || c == '_'
               || c == '.'
    first = TMC.letterChar <|> TM.satisfy w4symbol
    rest = TMC.alphaNumChar <|> TM.satisfy w4symbol

parseNat :: Parser Natural
parseNat = do
  _ <- TMC.string "#u"
  TMCL.decimal

parseInt :: Parser Integer
parseInt = TMCL.decimal <|> (negate <$> (TMC.char '-' *> TMCL.decimal))

parseReal :: Parser Rational
parseReal = do
  _ <- TMC.string "#r"
  n <- TMCL.decimal
  _ <- TMC.char '/'
  d <- TMCL.decimal
  return (n % d)

parseBV :: Parser (Int, Integer)
parseBV = do
  _ <- TMC.char '#'
  t <- TM.anySingle
  case t of
    'b' -> parseBin 0 0
    'x' -> parseHex
    _ -> MF.fail ("Invalid bitvector class: " ++ show t)
  where
    parseBin :: Int -> Integer -> Parser (Int, Integer)
    parseBin !nBits !value= do
      mb <- TM.optional TMC.binDigitChar
      case mb of
        Nothing -> return (nBits, value)
        Just bitChar -> parseBin (nBits + 1) (value * 2 + if bitChar == '1' then 1 else 0)
    parseHex :: Parser (Int, Integer)
    parseHex = do
      digits <- TM.some TMC.hexDigitChar
      return (length digits * 4, read ("0x" ++ digits))

parseBool :: Parser Bool
parseBool = do
  _ <- TMC.char '#'
  TM.try (TMC.string "true" *> return True) <|> (TMC.string "false" *> return False)

parseStrInfo :: Parser (Some WT.StringInfoRepr)
parseStrInfo = TM.try (TMC.string "#char16" >> return (Some WT.Char16Repr))
           <|> TM.try (TMC.string "#char8" >> return (Some WT.Char8Repr))
           <|> return (Some WT.UnicodeRepr)

parseStr :: Parser (Some WT.StringInfoRepr, T.Text)
parseStr = do
  prefix <- parseStrInfo
  _ <- TMC.char '"'
  str <- concat <$> TM.many (parseEscaped <|> TM.some (TM.noneOf ('"':"\\")))
  _ <- TMC.char '"'
  return (prefix, T.pack str)
  where
    parseEscaped = do
      _ <- TMC.char '\\'
      c <- TM.anySingle
      return ['\\', c]

parseFloat :: Parser (Some WT.FloatPrecisionRepr, BF.BigFloat)
parseFloat = do
  _ <- TMC.string "#f#"
  -- We printed the nat reprs out in decimal
  eb :: Natural
     <- TMCL.decimal
  _ <- TMC.char '#'
  sb :: Natural
     <- TMCL.decimal
  _ <- TMC.char '#'

  -- The float value itself is printed out as a hex literal
  hexDigits <- TM.some TMC.hexDigitChar

  Some ebRepr <- return (PN.mkNatRepr eb)
  Some sbRepr <- return (PN.mkNatRepr sb)
  case (PN.testLeq (PN.knownNat @2) ebRepr, PN.testLeq (PN.knownNat @2) sbRepr) of
    (Just PN.LeqProof, Just PN.LeqProof) -> do
      let rep = WT.FloatingPointPrecisionRepr ebRepr sbRepr

      -- We know our format: it is determined by the exponent bits (eb) and the
      -- significand bits (sb) parsed above
      let fmt = BF.precBits (fromIntegral sb) <> BF.expBits (fromIntegral eb)
      let (bf, status) = BF.bfFromString 16 fmt hexDigits
      case status of
        BF.Ok -> return (Some rep, bf)
        _ -> TM.fancyFailure (Set.singleton (TM.ErrorCustom (ErrorParsingHexFloat hexDigits)))
    _ -> TM.fancyFailure (Set.singleton (TM.ErrorCustom (InvalidExponentOrSignificandSize eb sb)))


parseAtom :: Parser WST.Atom
parseAtom = TM.try (uncurry WST.ABV <$> parseBV)
        <|> TM.try (WST.ABool <$> parseBool)
        <|> TM.try (WST.AInt <$> parseInt)
        <|> TM.try (WST.AId <$> parseId)
        <|> TM.try (WST.ANat <$> parseNat)
        <|> TM.try (WST.AReal <$> parseReal)
        <|> TM.try (uncurry WST.AStr <$> parseStr)
        <|> TM.try (uncurry WST.AFloat <$> parseFloat)

ws :: Parser ()
ws = TMCL.space TMC.space1 (TMCL.skipLineComment (T.pack ";")) empty

lexeme :: Parser a -> Parser a
lexeme = TMCL.lexeme ws

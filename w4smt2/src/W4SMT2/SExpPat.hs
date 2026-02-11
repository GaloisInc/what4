{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module W4SMT2.SExpPat
  ( sexp
  , stripPrefix
  , parseAtomInteger
  , stripPrefixInteger
  ) where

import Data.Char qualified as Char
import Data.List (stripPrefix)
import Data.Text qualified as Text
import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Quote qualified as TH

import What4.Protocol.SExp qualified as SExp

-- | Helper function to strip a prefix from an SExp.SAtom and return the suffix
stripAtomPrefix :: String -> SExp.SExp -> Maybe String
stripAtomPrefix prefix (SExp.SAtom atom) =
  Text.unpack <$> Text.stripPrefix (Text.pack prefix) atom
stripAtomPrefix _ _ = Nothing

-- | Helper function to parse an SExp.SAtom as an Integer
parseAtomInteger :: SExp.SExp -> Maybe Integer
parseAtomInteger (SExp.SAtom atom) = case reads (Text.unpack atom) of
  [(n, "")] -> Just n
  _ -> Nothing
parseAtomInteger _ = Nothing

-- | Helper function to strip a prefix from an SExp.SAtom and parse the suffix as Integer
stripPrefixInteger :: String -> SExp.SExp -> Maybe Integer
stripPrefixInteger prefix (SExp.SAtom atom) =
  case Text.stripPrefix (Text.pack prefix) atom of
    Just suffix -> case reads (Text.unpack suffix) of
      [(n, "")] -> Just n
      _ -> Nothing
    Nothing -> Nothing
stripPrefixInteger _ _ = Nothing

-- | 'TH.QuasiQuoter' for S-expression patterns.
--
-- Use @#name@ to bind a variable in the pattern.
-- Use @...name@ to bind a list of remaining elements (must be last in a list).
-- Use @prefix#name@ to match an atom that starts with prefix and bind the suffix to name.
-- Use @$name@ to match an atom and parse it as an Integer.
-- Use @prefix$name@ to match an atom that starts with prefix and parse the suffix as an Integer.
--
-- Examples:
--
-- @
-- [sexp|(= #e1 #e2)|]                    -- matches (= <e1> <e2>)
-- [sexp|(declare-const #n #t)|]          -- matches (declare-const <n> <t>)
-- [sexp|true|]                           -- matches the atom "true"
-- [sexp|(and ...args)|]                  -- matches (and <args...>)
-- [sexp|(#_ bv#w #s)|]                   -- matches (_ bv<w> <s>) where w is bound to the part after "bv"
-- [sexp|((#_ extract #h #l) #e)|]        -- matches ((_ extract <h> <l>) <e>) for bitvector extract
-- [sexp|($x)|]                           -- matches a single-element list with an atom that parses to an Integer
-- [sexp|(#_ bv$w)|]                      -- matches (_ bv<w>) where w is the part after "bv" parsed as Integer
-- @
sexp :: TH.QuasiQuoter
sexp = TH.QuasiQuoter
  { TH.quoteExp = \_ -> fail "sexp quasiquoter can only be used in patterns"
  , TH.quotePat = parseSExpPat
  , TH.quoteType = \_ -> fail "sexp quasiquoter can only be used in patterns"
  , TH.quoteDec = \_ -> fail "sexp quasiquoter can only be used in patterns"
  }

-- | Parse an S-expression pattern from a string
parseSExpPat :: String -> TH.Q TH.Pat
parseSExpPat input = do
  tokens <- tokenize input
  (pat, remaining) <- parsePatTokens tokens
  case remaining of
    [] -> return pat
    _ -> fail $ "Unexpected tokens after S-expression: " ++ show remaining

-- | Token type for parsing
data Token
  = TokLParen
  | TokRParen
  | TokAtom String
  | TokVar String      -- #variable
  | TokVarList String  -- ...variable
  | TokString String
  | TokPrefixVar String String  -- prefix#variable (e.g., bv#w)
  | TokIntVar String   -- $variable - parse atom as Integer
  | TokPrefixIntVar String String  -- prefix$variable (e.g., bv$w) - parse suffix as Integer
  deriving (Show, Eq)

-- | Tokenize the input string
tokenize :: String -> TH.Q [Token]
tokenize = go
  where
    go :: String -> TH.Q [Token]
    go [] = return []
    go (c:cs)
      | Char.isSpace c = go cs
      | c == '(' = (TokLParen :) <$> go cs
      | c == ')' = (TokRParen :) <$> go cs
      | c == '#' = do
          let (name, rest) = span isIdentChar cs
          if null name
            then fail "Expected variable name after #"
            else (TokVar name :) <$> go rest
      | c == '$' = do
          let (name, rest) = span isIdentChar cs
          if null name
            then fail "Expected variable name after $"
            else (TokIntVar name :) <$> go rest
      | c == '.' && take 2 cs == ".." = do
          let (name, rest) = span isIdentChar (drop 2 cs)
          if null name
            then fail "Expected variable name after ..."
            else (TokVarList name :) <$> go rest
      | c == '"' = do
          let (str, rest) = parseString cs
          (TokString str :) <$> go rest
      | otherwise = do
          let (atom, rest) = span isAtomChar (c:cs)
          -- Check if this atom contains # or $ (prefix patterns)
          case break (\ch -> ch == '#' || ch == '$') atom of
            (prefix, '#':varPart) | not (null prefix) && not (null varPart) ->
              (TokPrefixVar prefix varPart :) <$> go rest
            (prefix, '$':varPart) | not (null prefix) && not (null varPart) ->
              (TokPrefixIntVar prefix varPart :) <$> go rest
            _ -> (TokAtom atom :) <$> go rest

    isAtomChar :: Char -> Bool
    isAtomChar c' = not (Char.isSpace c') && c' /= '(' && c' /= ')' && c' /= '"'

    isIdentChar :: Char -> Bool
    isIdentChar c' = Char.isAlphaNum c' || c' == '_' || c' == '\''

    parseString :: String -> (String, String)
    parseString [] = ("", "")
    parseString ('"':rest) = ("", rest)
    parseString ('\\':c':rest) =
      let (str, remaining) = parseString rest
      in (c':str, remaining)
    parseString (c':rest) =
      let (str, remaining) = parseString rest
      in (c':str, remaining)

-- | Result of parsing a list - either a fixed list or a list with a tail variable
data ListResult
  = FixedList [TH.Pat]
  | ListWithTail [TH.Pat] TH.Name

-- | Parse tokens into a pattern
parsePatTokens :: [Token] -> TH.Q (TH.Pat, [Token])
parsePatTokens [] = fail "Unexpected end of input"
parsePatTokens (TokLParen : rest) = do
  (listResult, afterList) <- parseList rest
  let pat = case listResult of
        FixedList elements ->
          TH.ConP 'SExp.SApp [] [TH.ListP elements]
        ListWithTail elements tailVar ->
          TH.ConP 'SExp.SApp [] [foldr consP (TH.VarP tailVar) elements]
  return (pat, afterList)
  where
    consP :: TH.Pat -> TH.Pat -> TH.Pat
    consP h t = TH.InfixP h '(:) t
parsePatTokens (TokVar name : rest) = do
  let pat = TH.VarP (TH.mkName name)
  return (pat, rest)
parsePatTokens (TokVarList _ : _) =
  fail "Variadic pattern (...) can only appear inside a list"
parsePatTokens (TokAtom atom : rest) = do
  let pat = TH.ConP 'SExp.SAtom [] [TH.LitP (TH.StringL atom)]
  return (pat, rest)
parsePatTokens (TokString str : rest) = do
  let pat = TH.ConP 'SExp.SString [] [TH.LitP (TH.StringL str)]
  return (pat, rest)
parsePatTokens (TokPrefixVar prefix varName : rest) = do
  -- Create a view pattern: (stripAtomPrefix prefix -> Just #varName)
  -- This applies stripAtomPrefix to extract the suffix after the prefix
  let viewFn = TH.AppE (TH.VarE 'stripAtomPrefix) (TH.LitE (TH.StringL prefix))
  let pat = TH.ViewP viewFn (TH.ConP 'Just [] [TH.VarP (TH.mkName varName)])
  return (pat, rest)
parsePatTokens (TokIntVar varName : rest) = do
  -- Create a view pattern: (parseAtomInteger -> Just #varName)
  -- This applies parseAtomInteger to extract and parse the integer value
  let viewFn = TH.VarE 'parseAtomInteger
  let pat = TH.ViewP viewFn (TH.ConP 'Just [] [TH.VarP (TH.mkName varName)])
  return (pat, rest)
parsePatTokens (TokPrefixIntVar prefix varName : rest) = do
  -- Create a view pattern: (stripPrefixInteger prefix -> Just #varName)
  -- This applies stripPrefixInteger to extract and parse the suffix as an integer
  let viewFn = TH.AppE (TH.VarE 'stripPrefixInteger) (TH.LitE (TH.StringL prefix))
  let pat = TH.ViewP viewFn (TH.ConP 'Just [] [TH.VarP (TH.mkName varName)])
  return (pat, rest)
parsePatTokens (TokRParen : _) = fail "Unexpected ')'"

-- | Parse a list of S-expressions until we hit a closing paren
parseList :: [Token] -> TH.Q (ListResult, [Token])
parseList [] = fail "Unexpected end of input, expected ')'"
parseList (TokRParen : rest) = return (FixedList [], rest)
parseList (TokVarList name : TokRParen : rest) =
  return (ListWithTail [] (TH.mkName name), rest)
parseList (TokVarList _ : _) =
  fail "Variadic pattern (...) must be last in a list"
parseList tokens = do
  (element, afterElement) <- parsePatTokens tokens
  (listResult, afterList) <- parseList afterElement
  case listResult of
    FixedList elements -> return (FixedList (element : elements), afterList)
    ListWithTail elements tailVar -> return (ListWithTail (element : elements) tailVar, afterList)

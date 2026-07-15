-----------------------------------------------------------------------
-- |
-- Module           : What4.QQ
-- Description      : Quasiquoters for What4 symbolic expressions
-- Copyright        : (c) Galois, Inc 2026
-- License          : BSD3
-- Maintainer       : Langston Barrett <langston@galois.com>
-- Stability        : provisional
--
-- This module provides the 'w4' Template Haskell quasiquoter for building What4
-- symbolic expressions using a small, readable s-expression syntax, extended
-- with metavariables that splice in-scope Haskell values.
--
-- Parsing and code generation happen entirely at compile time: the quasiquoter
-- parses its body to an s-expression and emits a tree of "What4.Interface"
-- builder calls.
--
-- A quoted term elaborates to a function of the symbolic backend:
--
-- > [w4| add $x $y |] :: (IsExprBuilder sym, 1 <= w) => sym -> IO (SymBV sym w)
--
-- == Metavariables
--
-- [@\$name@]: An /expression/ metavariable. Splices the in-scope Haskell
--   binding @name@, which must be a @'SymExpr' sym tp@.
--
-- [@\@name@]: A /width/ metavariable. Splices the in-scope Haskell binding
--   @name@, which must be a @'NatRepr' w@. Used in bitvector-literal width
--   positions, e.g. @(bv \@w 42)@.
--
-- == Syntax
--
-- Boolean and bitvector operations share @and@, @or@, @xor@, and @not@.
-- Arithmetic uses @add@, @sub@, @neg@, @mul@, and @abs@; bitvector literals
-- are @(bv width value)@, @#b0101@, or @#xFF@. Signedness-sensitive
-- bitvector operations have explicit names such as @ult@ and @sdiv@.
-- Numeric operators do not implicitly coerce between Int and Real; see
-- "What4.QQ.Class".
--
-- The outermost application may omit its parentheses: @[w4| add $x $y |]@
-- is equivalent to @[w4| (add $x $y) |]@. Nested applications must remain
-- parenthesized.
--
-- == Operations
--
-- === Boolean
--
-- +----------------+------------+-----------------+-----------+
-- | Operation      | SMT-LIB    | What4.Serialize | w4        |
-- +================+============+=================+===========+
-- | and            | @and@      | @andp@          | @and@     |
-- +----------------+------------+-----------------+-----------+
-- | or             | @or@       | @orp@           | @or@      |
-- +----------------+------------+-----------------+-----------+
-- | not            | @not@      | @notp@          | @not@     |
-- +----------------+------------+-----------------+-----------+
-- | implies        | @=>@       | -               | @implies@ |
-- +----------------+------------+-----------------+-----------+
-- | xor            | @xor@      | @xorp@          | @xor@     |
-- +----------------+------------+-----------------+-----------+
-- | if-then-else   | @ite@      | @ite@           | @if@      |
-- +----------------+------------+-----------------+-----------+
-- | equal          | @=@        | @=@             | @eq@      |
-- +----------------+------------+-----------------+-----------+
-- | not equal      | @distinct@ | -               | @ne@      |
-- +----------------+------------+-----------------+-----------+
--
-- @eq@, @ne@, and @if@ work for every What4 base type; GHC checks that their
-- operands or branches have matching types.
--
-- === Integer and real
--
-- +------------------+------------+-----------------+-------+
-- | Operation        | SMT-LIB    | What4.Serialize | w4    |
-- +==================+============+=================+=======+
-- | add              | @+@        | @intadd@        | @add@ |
-- +------------------+------------+-----------------+-------+
-- | subtract         | @-@        | -               | @sub@ |
-- +------------------+------------+-----------------+-------+
-- | negate           | @-@        | -               | @neg@ |
-- +------------------+------------+-----------------+-------+
-- | multiply         | @*@        | @intmul@        | @mul@ |
-- +------------------+------------+-----------------+-------+
-- | divide           | @div@/@/@  | @intdiv@        | @div@ |
-- +------------------+------------+-----------------+-------+
-- | modulus (Int)    | @mod@      | @intmod@        | @mod@ |
-- +------------------+------------+-----------------+-------+
-- | absolute value   | @abs@      | @intabs@        | @abs@ |
-- +------------------+------------+-----------------+-------+
-- | less than        | @<@        | -               | @lt@  |
-- +------------------+------------+-----------------+-------+
-- | less or equal    | @<=@       | @intle@         | @le@  |
-- +------------------+------------+-----------------+-------+
-- | greater than     | @>@        | -               | @gt@  |
-- +------------------+------------+-----------------+-------+
-- | greater or equal | @>=@       | -               | @ge@  |
-- +------------------+------------+-----------------+-------+
--
-- @add@, @sub@, @neg@, and @mul@ also work on bitvectors. @div@ is overloaded
-- between Integer and Real; @mod@ is Integer-only. There are no implicit
-- Integer/Real coercions.
--
-- === Bitvector arithmetic and comparison
--
-- +---------------------+----------+-----------------+--------+
-- | Operation           | SMT-LIB  | What4.Serialize | w4     |
-- +=====================+==========+=================+========+
-- | unsigned divide     | @bvudiv@ | @bvudiv@        | @udiv@ |
-- +---------------------+----------+-----------------+--------+
-- | signed divide       | @bvsdiv@ | @bvsdiv@        | @sdiv@ |
-- +---------------------+----------+-----------------+--------+
-- | unsigned remainder  | @bvurem@ | @bvurem@        | @urem@ |
-- +---------------------+----------+-----------------+--------+
-- | signed remainder    | @bvsrem@ | @bvsrem@        | @srem@ |
-- +---------------------+----------+-----------------+--------+
-- | unsigned less than  | @bvult@  | @bvult@         | @ult@  |
-- +---------------------+----------+-----------------+--------+
-- | unsigned less/equal | @bvule@  | @bvule@         | @ule@  |
-- +---------------------+----------+-----------------+--------+
-- | unsigned greater    | @bvugt@  | @bvugt@         | @ugt@  |
-- +---------------------+----------+-----------------+--------+
-- | unsigned greater/eq | @bvuge@  | @bvuge@         | @uge@  |
-- +---------------------+----------+-----------------+--------+
-- | signed less than    | @bvslt@  | @bvslt@         | @slt@  |
-- +---------------------+----------+-----------------+--------+
-- | signed less/equal   | @bvsle@  | @bvsle@         | @sle@  |
-- +---------------------+----------+-----------------+--------+
-- | signed greater      | @bvsgt@  | @bvsgt@         | @sgt@  |
-- +---------------------+----------+-----------------+--------+
-- | signed greater/eq   | @bvsge@  | @bvsge@         | @sge@  |
-- +---------------------+----------+-----------------+--------+
--
-- === Bitvector bitwise, shift, and rotate
--
-- +------------------------+---------------+-----------------+--------+
-- | Operation              | SMT-LIB       | What4.Serialize | w4     |
-- +========================+===============+=================+========+
-- | and                    | @bvand@       | @bvand@         | @and@  |
-- +------------------------+---------------+-----------------+--------+
-- | or                     | @bvor@        | @bvor@          | @or@   |
-- +------------------------+---------------+-----------------+--------+
-- | xor                    | @bvxor@       | @bvxor@         | @xor@  |
-- +------------------------+---------------+-----------------+--------+
-- | complement             | @bvnot@       | @bvnot@         | @not@  |
-- +------------------------+---------------+-----------------+--------+
-- | shift left             | @bvshl@       | @bvshl@         | @shl@  |
-- +------------------------+---------------+-----------------+--------+
-- | logical shift right    | @bvlshr@      | @bvlshr@        | @lshr@ |
-- +------------------------+---------------+-----------------+--------+
-- | arithmetic shift right | @bvashr@      | @bvashr@        | @ashr@ |
-- +------------------------+---------------+-----------------+--------+
-- | rotate left            | @rotate_left@ | -               | @rol@  |
-- +------------------------+---------------+-----------------+--------+
-- | rotate right           | @rotate_right@| -               | @ror@  |
-- +------------------------+---------------+-----------------+--------+
--
-- === Bitvector literals and structure
--
-- +----------------+-----------------------+------------------------+----------------------+
-- | Operation      | SMT-LIB               | What4.Serialize        | w4                   |
-- +================+=======================+========================+======================+
-- | binary literal | @#b0101@              | @#b0101@               | @#b0101@             |
-- +----------------+-----------------------+------------------------+----------------------+
-- | hex literal    | @#xFF@                | @#xFF@                 | @#xFF@               |
-- +----------------+-----------------------+------------------------+----------------------+
-- | sized literal  | @(_ bv42 16)@         | @#b...@/@#x...@        | @bv 16 42@           |
-- |                |                       |                        | @(bv \@w 42)@        |
-- +----------------+-----------------------+------------------------+----------------------+
-- | concatenate    | @concat@              | @concat@               | @concat@             |
-- +----------------+-----------------------+------------------------+----------------------+
-- | extract        | @(_ extract hi lo) x@ | @(_ extract hi lo) x@  | @extract hi lo x@    |
-- +----------------+-----------------------+------------------------+----------------------+
-- | zero extend    | @(_ zero_extend n) x@ | @(_ zero_extend n) x@  | @zext n x@           |
-- +----------------+-----------------------+------------------------+----------------------+
-- | sign extend    | @(_ sign_extend n) x@ | @(_ sign_extend n) x@  | @sext n x@           |
-- +----------------+-----------------------+------------------------+----------------------+
--
-- In @w4@, a sized literal is width-first: @bv 16 42@ denotes the 16-bit value
-- 42. @extract@, @zext@, and @sext@ drop SMT-LIB's indexed identifier wrapper.
--
-- == Evaluation order
--
-- The generated code evaluates ordinary operator arguments from left to right,
-- exactly once each, before invoking the corresponding What4 builder. For @(let
-- ((v e) ...) body)@, the right-hand sides are likewise evaluated from left
-- to right, but each is evaluated in the enclosing environment: bindings are
-- parallel, as in SMT-LIB, and become visible only in @body@.
--
-- Because the generated code contains type-level natural-number literals
-- and type applications, modules that use these quasiquoters typically need
-- @DataKinds@, @TypeApplications@, and @TypeOperators@ enabled.
-----------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module What4.QQ
  ( w4
  , dumpW4
    -- * Runtime helpers used by generated code
  , qqZext
  , qqSext
  ) where

import           Control.Monad (foldM)
import qualified Data.Attoparsec.Text as AT
import qualified Data.BitVector.Sized as BV
import           Data.Char (isAlpha, isAlphaNum, isDigit, isUpper)
import           Data.List (foldl')
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Text (Text)
import qualified Data.Text as Text
import           GHC.TypeNats (type (<=), type (+))

import           Language.Haskell.TH hiding (Pred)
import           Language.Haskell.TH.Quote (QuasiQuoter(..))
import           Language.Haskell.TH.Syntax (lift)

import qualified Data.Parameterized.NatRepr as NR

import           What4.Interface (IsExprBuilder, SymBV)
import qualified What4.Interface as WI
import           What4.Protocol.ReadDecimal (readDecimal)
import           What4.Protocol.SExp (SExp(..), stringToSExp)
import           What4.QQ.Class
                   ( sortAdd, sortSub, sortMul, sortNeg, sortAbs, sortLt, sortLe
                   , sortDiv, sortAnd, sortOr, sortXor, sortNot )

-- | Zero-extend, adding a statically-known number of bits. The type-level
-- proof plumbing is what makes @(zext n e)@ elaborate to a
-- well-typed 'WI.bvZext' call.
qqZext ::
  forall sym w n.
  (IsExprBuilder sym, 1 <= w, 1 <= n) =>
  sym -> NR.NatRepr n -> SymBV sym w -> IO (SymBV sym (w + n))
qqZext sym n x =
  case NR.leqAdd2 (NR.leqRefl (WI.bvWidth x)) (NR.LeqProof @1 @n) of
    NR.LeqProof -> WI.bvZext sym (NR.addNat (WI.bvWidth x) n) x

-- | Sign-extend, adding a statically-known number of bits. See 'qqZext'.
qqSext ::
  forall sym w n.
  (IsExprBuilder sym, 1 <= w, 1 <= n) =>
  sym -> NR.NatRepr n -> SymBV sym w -> IO (SymBV sym (w + n))
qqSext sym n x =
  case NR.leqAdd2 (NR.leqRefl (WI.bvWidth x)) (NR.LeqProof @1 @n) of
    NR.LeqProof -> WI.bvSext sym (NR.addNat (WI.bvWidth x) n) x

-- | Quasiquoter for What4 expressions. The quoted body is parsed as a
-- single s-expression and elaborated to
-- @('IsExprBuilder' sym) => sym -> IO ('SymExpr' sym tp)@, where @tp@ is
-- inferred from the term. See the module documentation for the syntax and
-- for metavariable conventions.
w4 :: QuasiQuoter
w4 = exprOnly "w4" compileString

-- | Pretty-print the Haskell code that 'w4' would generate for a snippet,
-- as a 'String'. Module qualifiers are stripped (see 'simplifyNames') so the
-- output reads like hand-written code. Intended for tests and debugging:
--
-- > $(dumpW4 "add #b0011 #b0001") :: String
dumpW4 :: String -> Q Exp
dumpW4 str = do
  e <- compileString str
  lift (simplifyNames (pprint e))

-- | Drop module qualifiers from a pretty-printed expression so it reads like
-- hand-written source: @What4.Interface.bvAdd@ becomes @bvAdd@,
-- @Data.Parameterized.NatRepr.Internal.knownNat@ becomes @knownNat@.
--
-- 'pprint' renders a qualified name as dot-separated components with no
-- surrounding spaces, the leading ones being module names (always
-- uppercase-initial); we keep only the final component. A dotted run whose
-- first component is /not/ uppercase (e.g. the real literal @4.5@) is left
-- untouched.
simplifyNames :: String -> String
simplifyNames = go
  where
    isNameStart c = isAlpha c || c == '_'
    isNameChar  c = isAlphaNum c || c == '_' || c == '\'' || c == '.'

    go [] = []
    go s@(c : rest)
      | isNameStart c =
          let (tok, more) = span isNameChar s
          in stripQual tok ++ go more
      | otherwise = c : go rest

    -- Given a maximal identifier-or-dot run, keep only the final
    -- (dot-separated) component when it is a module-qualified name.
    stripQual tok
      | '.' `elem` tok =
          case splitDots tok of
            seg0 : rest ->
              case (seg0, reverse rest) of
                (c : _, final : _) | isUpper c -> final
                _ -> tok
            [] -> tok
      | otherwise = tok

    splitDots t =
      case break (== '.') t of
        (pre, '.' : suf) -> pre : splitDots suf
        (pre, _)         -> [pre]

-- | Build a 'QuasiQuoter' that only supports expression contexts.
exprOnly :: String -> (String -> Q Exp) -> QuasiQuoter
exprOnly name qe =
  QuasiQuoter
  { quoteExp  = qe
  , quotePat  = \_ -> fail (name ++ " may only be used as an expression")
  , quoteType = \_ -> fail (name ++ " may only be used as an expression")
  , quoteDec  = \_ -> fail (name ++ " may only be used as an expression")
  }

-- | Parse a snippet and generate @\\sym -> body@.
compileString :: String -> Q Exp
compileString str = do
  sexps <- stringToSExp readString str
  sexp <-
    case sexps of
      [s] -> pure s
      []  -> fail "what4-qq: empty quasiquote"
      ss  -> pure (SApp ss)
  symN <- newName "sym"
  lamE [varP symN] (compile symN Map.empty sexp)
  where
    readString :: AT.Parser Text
    readString = AT.char '"' *> AT.takeWhile (/= '"') <* AT.char '"'

-- | The compile-time code generator. Each node elaborates to a Haskell
-- expression of type @IO ('SymExpr' sym tp)@.
--
-- The @env@ maps @let@-bound source names to the fresh Haskell 'Name's
-- holding their (already-evaluated) values.
compile :: Name -> Map Text Name -> SExp -> Q Exp
compile sym env = go
  where
    symE :: Q Exp
    symE = varE sym

    -- Bind each sub-expression to a fresh name, then hand the names to a
    -- continuation that builds the final call. Produces a readable
    -- do-block in @-ddump-splices@.
    bindAll :: [SExp] -> ([Name] -> Q Exp) -> Q Exp
    bindAll subs k = do
      ns <- mapM (const (newName "e")) subs
      doE (zipWith (\n s -> bindS (varP n) (go s)) ns subs ++ [noBindS (k ns)])

    bindOne :: SExp -> (Name -> Q Exp) -> Q Exp
    bindOne a k = do
      x <- newName "e"
      doE [bindS (varP x) (go a), noBindS (k x)]

    bindTwo :: SExp -> SExp -> (Name -> Name -> Q Exp) -> Q Exp
    bindTwo a b k = do
      x <- newName "e"
      y <- newName "e"
      doE
        [ bindS (varP x) (go a)
        , bindS (varP y) (go b)
        , noBindS (k x y)
        ]

    bindThree :: SExp -> SExp -> SExp -> (Name -> Name -> Name -> Q Exp) -> Q Exp
    bindThree a b c k = do
      x <- newName "e"
      y <- newName "e"
      z <- newName "e"
      doE
        [ bindS (varP x) (go a)
        , bindS (varP y) (go b)
        , bindS (varP z) (go c)
        , noBindS (k x y z)
        ]

    -- A binary call @f sym a b@.
    binop :: Name -> SExp -> SExp -> Q Exp
    binop f a b = bindTwo a b $ \x y ->
      appE (appE (appE (varE f) symE) (varE x)) (varE y)

    -- A binary call with the arguments flipped (@f sym b a@).
    binopFlip :: Name -> SExp -> SExp -> Q Exp
    binopFlip f a b = bindTwo a b $ \x y ->
      appE (appE (appE (varE f) symE) (varE y)) (varE x)

    -- A unary call @f sym a@.
    unop :: Name -> SExp -> Q Exp
    unop f a = bindOne a $ \x ->
      appE (appE (varE f) symE) (varE x)

    -- Left-fold a non-empty argument list with a binary builder,
    -- e.g. @foldM (f sym) e0 [e1, e2]@.
    foldNary :: Name -> [SExp] -> Q Exp
    foldNary f args = bindAll args $ \case
      []       -> fail "what4-qq: operator requires at least one argument"
      [n0, n1] ->
        appE (appE (appE (varE f) symE) (varE n0)) (varE n1)
      (n0:ns)  ->
        appE (appE (appE (varE 'foldM) (appE (varE f) symE)) (varE n0))
             (listE (map varE ns))

    -- Emit an @IO@ node building a bitvector literal of the given width
    -- (as a @Q Exp@ producing a 'NatRepr') and integer value. The width
    -- expression is duplicated, which is safe: it is always either
    -- @knownNat \@w@ or a plain variable reference.
    bvLitNode :: Q Exp -> Integer -> Q Exp
    bvLitNode widthE val =
      appE (appE (appE (varE 'WI.bvLit) symE) widthE)
           (appE (appE (varE 'BV.mkBV) widthE) (litE (integerL val)))

    go :: SExp -> Q Exp
    go = \case
      SAtom t -> goAtom t
      SString _ -> fail "what4-qq: string literals are not supported"
      SApp [] -> fail "what4-qq: empty application"
      SApp (hd : args) -> goApp hd args

    -- Atoms: metavariables, literals, and let-bound names.
    goAtom :: Text -> Q Exp
    goAtom t
      | Just base <- Text.stripPrefix "$" t = exprMetavar base
      | t == "true"  = pureE (appE (varE 'WI.truePred) symE)
      | t == "false" = pureE (appE (varE 'WI.falsePred) symE)
      | Just bits <- Text.stripPrefix "#b" t = binBVLit bvLitNode bits
      | Just hex  <- Text.stripPrefix "#x" t = hexBVLit bvLitNode hex
      | Just n <- Map.lookup t env = pureE (varE n)
      | Just i <- readIntLit t = appE (appE (varE 'WI.intLit) symE) (litE (integerL i))
      | Just r <- readRealLit t = appE (appE (varE 'WI.realLit) symE) (litE (rationalL r))
      | otherwise = fail ("what4-qq: unknown atom: " ++ Text.unpack t)

    exprMetavar :: Text -> Q Exp
    exprMetavar base
      | Text.null base = fail "what4-qq: empty $ metavariable name"
      | otherwise = pureE (varE (mkName (Text.unpack base)))

    -- Applications, dispatched on the head.
    goApp :: SExp -> [SExp] -> Q Exp
    goApp hd args =
      case hd of
        SApp _    -> fail "what4-qq: application head must be an operator"
        SAtom op  -> goOp op args
        SString _ -> fail "what4-qq: unsupported application head"

    -- (extract hi lo e) => bvSelect sym (knownNat @lo) (knownNat @{hi-lo+1}) e
    extractE :: Integer -> Integer -> SExp -> Q Exp
    extractE hi lo e
      | hi < lo || lo < 0 = fail "what4-qq: invalid extract bounds"
      | otherwise = bindOne e $ \x ->
          appE (appE (appE (appE (varE 'WI.bvSelect) symE)
                           (knownNatE lo))
                     (knownNatE (hi - lo + 1)))
               (varE x)

    -- (zext n e) / (sext n e)
    extendE :: Name -> Integer -> SExp -> Q Exp
    extendE f n e = bindOne e $ \x ->
      appE (appE (appE (varE f) symE) (knownNatE n)) (varE x)

    -- Non-indexed operators.
    goOp :: Text -> [SExp] -> Q Exp
    goOp op args =
      case (op, args) of
        ("not", [a])          -> unop 'sortNot a
        ("implies", [a, b])   -> binop 'WI.impliesPred a b
        ("and", _)            -> foldNary 'sortAnd args
        ("or", _)             -> foldNary 'sortOr args
        ("xor", _)            -> foldNary 'sortXor args
        ("eq", [a, b])        -> binop 'WI.isEq a b
        ("ne", [a, b])        -> bindTwo a b $ \x y ->
          [| WI.notPred $(symE) =<< WI.isEq $(symE) $(varE x) $(varE y) |]
        ("if", [c, t, e])     -> bindThree c t e $ \x y z ->
          appE (appE (appE (appE (varE 'WI.baseTypeIte) symE) (varE x)) (varE y)) (varE z)

        -- Overloaded arithmetic (NumSort / OrdSort), no coercion.
        ("add", _)            -> foldNary 'sortAdd args
        ("mul", _)            -> foldNary 'sortMul args
        ("sub", [a])          -> unop 'sortNeg a
        ("sub", a:rest@(_:_)) -> foldNary 'sortSub (a : rest)
        ("neg", [a])          -> unop 'sortNeg a
        ("abs", [a])          -> unop 'sortAbs a
        ("lt", [a, b])        -> binop 'sortLt a b
        ("le", [a, b])        -> binop 'sortLe a b
        ("gt", [a, b])        -> binopFlip 'sortLt a b
        ("ge", [a, b])        -> binopFlip 'sortLe a b

        ("div", [a, b])       -> binop 'sortDiv a b
        ("mod", [a, b])       -> binop 'WI.intMod a b

        -- Bitvectors.
        ("concat", [a, b])    -> binop 'WI.bvConcat a b
        ("let", [binds, bdy]) -> goLet binds bdy

        ("bv", [wsexp, SAtom val])
          | Just n <- readIntLit val -> bvLitNode (widthArg wsexp) n
        ("extract", [hi, lo, e])
          | Just hiN <- widthLit hi, Just loN <- widthLit lo ->
              extractE hiN loN e
        ("zext", [n, e])
          | Just nN <- widthLit n -> extendE 'qqZext nN e
        ("sext", [n, e])
          | Just nN <- widthLit n -> extendE 'qqSext nN e

        _ | Just f <- Map.lookup op bvBinops
          , [a, b] <- args    -> binop f a b

        _ -> fail ("what4-qq: unsupported operator or arity: " ++ Text.unpack op)

    -- (let ((v e) ...) body). SMT-LIB let is parallel: all right-hand
    -- sides are compiled under the current env, then env is extended.
    goLet :: SExp -> SExp -> Q Exp
    goLet binds bdy =
      case binds of
        SApp pairs -> do
          parsed <- mapM parseBind pairs
          ns <- mapM (const (newName "v")) parsed
          let env' = foldl' (\m ((v, _), n) -> Map.insert v n m) env (zip parsed ns)
              stmts = [ bindS (varP n) (go rhs) | (n, (_, rhs)) <- zip ns parsed ]
          doE (stmts ++ [noBindS (compile sym env' bdy)])
        _ -> fail "what4-qq: let bindings must be a list"
      where
        parseBind = \case
          SApp [SAtom v, rhs] -> pure (v, rhs)
          _ -> fail "what4-qq: malformed let binding"

    -- Width arguments: @\@w@ splices a NatRepr; a decimal is a knownNat.
    widthArg :: SExp -> Q Exp
    widthArg = \case
      SAtom t
        | Just base <- Text.stripPrefix "@" t ->
            if Text.null base
              then fail "what4-qq: empty @ metavariable name"
              else varE (mkName (Text.unpack base))
        | Just n <- readIntLit t -> knownNatE n
      other -> fail ("what4-qq: expected a width, got " ++ show other)

    pureE :: Q Exp -> Q Exp
    pureE = appE (varE 'pure)

-- | Emit @knownNat \@n@.
knownNatE :: Integer -> Q Exp
knownNatE n = appTypeE (varE 'NR.knownNat) (litT (numTyLit n))

-- | Decimal literal appearing in an index position (@extract@\/@extend@),
-- which must be a compile-time constant, not a metavariable.
widthLit :: SExp -> Maybe Integer
widthLit (SAtom t) = readIntLit t
widthLit _ = Nothing

-- | Parse a non-negative decimal integer literal.
readIntLit :: Text -> Maybe Integer
readIntLit t
  | not (Text.null t) && Text.all isDigit t =
      case reads (Text.unpack t) of
        [(n, "")] -> Just n
        _ -> Nothing
  | otherwise = Nothing

-- | Parse a decimal real literal (must contain a @.@).
readRealLit :: Text -> Maybe Rational
readRealLit t
  | Text.any (== '.') t =
      case readDecimal (Text.unpack t) of
        Just (r, "") -> Just r
        _ -> Nothing
  | otherwise = Nothing

-- | @#b0101@: value and width (in bits) taken from the binary digits.
binBVLit :: (Q Exp -> Integer -> Q Exp) -> Text -> Q Exp
binBVLit mk bits
  | Text.null bits = fail "what4-qq: empty #b literal"
  | not (Text.all (`elem` ("01" :: String)) bits) =
      fail ("what4-qq: invalid #b literal: #b" ++ Text.unpack bits)
  | otherwise = mk (knownNatE (fromIntegral (Text.length bits))) (binToInteger bits)

-- | @#xFF@: value from the hex digits, width four bits per digit.
hexBVLit :: (Q Exp -> Integer -> Q Exp) -> Text -> Q Exp
hexBVLit mk hex
  | Text.null hex = fail "what4-qq: empty #x literal"
  | not (Text.all isHexDigit hex) =
      fail ("what4-qq: invalid #x literal: #x" ++ Text.unpack hex)
  | otherwise = mk (knownNatE (4 * fromIntegral (Text.length hex))) (hexToInteger hex)
  where isHexDigit c = c `elem` ("0123456789abcdefABCDEF" :: String)

-- | Convert a string of @'0'@\/@'1'@ to an 'Integer'.
binToInteger :: Text -> Integer
binToInteger = Text.foldl' (\acc c -> acc * 2 + if c == '1' then 1 else 0) 0

-- | Convert a hexadecimal string to an 'Integer'.
hexToInteger :: Text -> Integer
hexToInteger t = read ("0x" ++ Text.unpack t)

-- | Binary bitvector operators, mapped to their "What4.Interface"
-- builders. Division/remainder use the SMT-LIB total variants so the
-- abstract domains match the spec.
bvBinops :: Map Text Name
bvBinops = Map.fromList
  [ ("udiv", 'WI.bvUdivSmtlib)
  , ("sdiv", 'WI.bvSdivSmtlib)
  , ("urem", 'WI.bvUremSmtlib)
  , ("srem", 'WI.bvSremSmtlib)
  , ("shl",  'WI.bvShl)
  , ("lshr", 'WI.bvLshr)
  , ("ashr", 'WI.bvAshr)
  , ("rol",  'WI.bvRol)
  , ("ror",  'WI.bvRor)
  , ("ult",  'WI.bvUlt)
  , ("slt",  'WI.bvSlt)
  , ("ule",  'WI.bvUle)
  , ("sle",  'WI.bvSle)
  , ("ugt",  'WI.bvUgt)
  , ("sgt",  'WI.bvSgt)
  , ("uge",  'WI.bvUge)
  , ("sge",  'WI.bvSge)
  ]

------------------------------------------------------------------------
-- |
-- Module           : What4.Protocol.SMTLib2
-- Description      : Interface for solvers that consume SMTLib2
-- Copyright        : (c) Galois, Inc 2014-2020
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module defines operations for producing SMTLib2-compatible
-- queries useful for interfacing with solvers that accecpt SMTLib2 as
-- an input language.
------------------------------------------------------------------------
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module What4.Protocol.SMTLib2
  ( -- SMTLib special purpose exports
    Writer
  , SMTLib2Tweaks(..)
  , newWriter
  , writeCheckSat
  , writeExit
  , writeGetValue
  , writeGetAbduct
  , writeGetAbductNext
  , runCheckSat
  , runGetAbducts
  , asSMT2Type
  , setOption
  , getVersion
  , versionResult
  , getName
  , nameResult
  , setProduceModels
  , smtLibEvalFuns
  , smtlib2Options
    -- * Logic
  , SMT2.Logic(..)
  , SMT2.qf_bv
  , SMT2.allSupported
  , all_supported
  , setLogic
    -- * Type
  , SMT2.Sort(..)
  , SMT2.arraySort
    -- * Term
  , Term(..)
  , arrayConst
  , What4.Protocol.SMTLib2.arraySelect
  , arrayStore
    -- * Solvers and External interface
  , Session(..)
  , SMTLib2GenericSolver(..)
  , writeDefaultSMT2
  , startSolver
  , shutdownSolver
  , smtAckResult
  , SMTLib2Exception(..)
    -- * Solver version
  , ppSolverVersionCheckError
  , ppSolverVersionError
  , checkSolverVersion
  , checkSolverVersion'
  , queryErrorBehavior
  , defaultSolverBounds
    -- * Re-exports
  , SMTWriter.WriterConn
  , SMTWriter.assume
  , SMTWriter.supportedFeatures
  , SMTWriter.nullAcknowledgementAction
  ) where

#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail( MonadFail )
#endif

import           Control.Applicative
import           Control.Exception
import           Control.Monad.State.Strict
import qualified Data.BitVector.Sized as BV
import           Data.Char (digitToInt, isAscii)
import           Data.IORef
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Monoid
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Pair
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import           Data.Ratio
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Lazy as Lazy
import           Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import qualified Data.Text.Lazy.Builder.Int as Builder

import           Numeric (readDec, readHex, readInt, showHex)
import           Numeric.Natural
import qualified System.Exit as Exit
import qualified System.IO as IO
import qualified System.IO.Streams as Streams
import           Data.Versions (Version(..))
import qualified Data.Versions as Versions
import qualified Prettyprinter as PP
import           LibBF( bfToBits )

import           Prelude hiding (writeFile)

import           What4.BaseTypes
import qualified What4.Config as CFG
import qualified What4.Expr.Builder as B
import           What4.Expr.GroundEval
import qualified What4.Interface as I
import           What4.ProblemFeatures
import           What4.Protocol.Online
import           What4.Protocol.ReadDecimal
import           What4.Protocol.SExp
import           What4.Protocol.SMTLib2.Syntax (Term, term_app, un_app, bin_app)

import           What4.Protocol.SMTLib2.Response
import qualified What4.Protocol.SMTLib2.Syntax as SMT2 hiding (Term)
import qualified What4.Protocol.SMTWriter as SMTWriter
import           What4.Protocol.SMTWriter hiding (assume, Term)
import           What4.SatResult
import           What4.Utils.FloatHelpers (fppOpts)
import           What4.Utils.HandleReader
import           What4.Utils.Process
import           What4.Utils.Versions
import           What4.Solver.Adapter

-- | Set the logic to all supported logics.
all_supported :: SMT2.Logic
all_supported = SMT2.allLogic
{-# DEPRECATED all_supported "Use allLogic instead" #-}


smtlib2Options :: [CFG.ConfigDesc]
smtlib2Options = smtParseOptions

------------------------------------------------------------------------
-- Floating point

data SMTFloatPrecision =
  SMTFloatPrecision { smtFloatExponentBits :: !Natural
                      -- ^ Number of bits in exponent
                    , smtFloatSignificandBits :: !Natural
                      -- ^ Number of bits in the significand.
                    }
  deriving (Eq, Ord)

asSMTFloatPrecision :: FloatPrecisionRepr fpp -> SMTFloatPrecision
asSMTFloatPrecision (FloatingPointPrecisionRepr eb sb) =
  SMTFloatPrecision { smtFloatExponentBits = natValue eb
                    , smtFloatSignificandBits = natValue sb
                    }

mkFloatSymbol :: Builder -> SMTFloatPrecision -> Builder
mkFloatSymbol nm (SMTFloatPrecision eb sb) =
  "(_ "
    <> nm
    <> " "
    <> fromString (show eb)
    <> " "
    <> fromString (show sb)
    <> ")"

------------------------------------------------------------------------
-- SMTLib2Tweaks

-- | Select a valued from a nested array
nestedArrayUpdate :: Term
                  -> (Term, [Term])
                  -> Term
                  -> Term
nestedArrayUpdate a (h,[]) v  = SMT2.store a h v
nestedArrayUpdate a (h,i:l) v = SMT2.store a h sub_a'
  where sub_a' = nestedArrayUpdate (SMT2.select a h) (i,l) v

arrayConst :: SMT2.Sort -> SMT2.Sort -> Term -> Term
arrayConst = SMT2.arrayConst

arraySelect :: Term -> Term -> Term
arraySelect = SMT2.select

arrayStore :: Term -> Term -> Term -> Term
arrayStore = SMT2.store

------------------------------------------------------------------------------------
-- String Escaping functions
--
-- The following functions implement the escaping and
-- escape parsing rules from SMTLib 2.6.  Documentation
-- regarding this format is pasted below from the
-- specification document.
--
--      String literals
--      All double-quote-delimited string literals consisting of printable US ASCII
--      characters, i.e., those with Unicode code point from 0x00020 to 0x0007E.
--      We refer to these literals as _string constants_.
--
--      The restriction to printable US ASCII characters in string constants is for
--      simplicity since that set is universally supported. Arbitrary Unicode characters
--      can be represented with _escape sequences_ which can have one of the following
--      forms
--          \ud₃d₂d₁d₀
--          \u{d₀}
--          \u{d₁d₀}
--          \u{d₂d₁d₀}
--          \u{d₃d₂d₁d₀}
--          \u{d₄d₃d₂d₁d₀}
--      where each dᵢ is a hexadecimal digit and d₄ is restricted to the range 0-2.
--      These are the **only escape sequences** in this theory. See later.
--      In a later version, the restrictions above on the digits may be extended
--      to allow characters from all 17 Unicode planes.
--
--      Observe that the first form, \ud₃d₂d₁d₀, has exactly 4 hexadecimal digit,
--      following the common use of this form in some programming languages.
--      Unicode characters outside the range covered by \ud₃d₂d₁d₀ can be
--      represented with the long form \u{d₄d₃d₂d₁d₀}.
--
--      Also observe that programming language-specific escape sequences, such as
--      \n, \b, \r and so on, are _not_ escape sequences in this theory as they
--      are not fully standard across languages.

-- | Apply the SMTLib2.6 string escaping rules to a string literal.
textToTerm :: Text -> Term
textToTerm bs = SMT2.T ("\"" <> Text.foldr f "\"" bs)
 where
 inLiteralRange c = 0x20 <= fromEnum c && fromEnum c <= 0x7E

 f c x
   -- special case: the `"` character has a special case escaping mode which
   -- is encoded as `""`
   | '\"' == c = "\"\"" <> x

   -- special case: always escape the `\` character as an explicit code point,
   -- so we don't have to do lookahead to discover if it is followed by a `u`
   | '\\' == c = "\\u{5c}" <> x

   -- others characters in the "normal" ASCII range require no escaping
   | inLiteralRange c = Builder.singleton c <> x

   -- characters outside that range require escaping
   | otherwise = "\\u{" <> Builder.fromString (showHex (fromEnum c) "}") <> x



-- | Parse SMTLIb2.6 escaping rules for strings.
--
--   Note! The escaping rule that uses the @\"\"@ sequence
--   to encode a double quote has already been resolved
--   by @parseSMTLIb2String@, so here we just need to
--   parse the @\\u@ escape forms.
unescapeText :: Text -> Maybe Text
unescapeText = go mempty
 where
 go str t =
   case Text.uncons t of
     Nothing -> Just str
     Just (c, t')
       | not (isAscii c) -> Nothing
       | c == '\\'       -> readEscape str t'
       | otherwise       -> continue str c t'

 continue str c t = go (Text.snoc str c) t

 readEscape str t =
   case Text.uncons t of
     Nothing -> Just (Text.snoc str '\\')
     Just (c, t')
       -- Note: the \u forms are the _only_ escape forms
       | c == 'u'  -> readHexEscape str t'
       | otherwise -> continue (Text.snoc str '\\') c t'

 readHexEscape str t =
   case Text.uncons t of
     Just (c, t')
       -- take until the closing brace
       | c == '{'
       , (ds, t'') <- Text.breakOn "}" t'
       , Just ('}',t''') <- Text.uncons t''
       -> readDigits str ds t'''

         -- take exactly four digits
       | (ds, t'') <- Text.splitAt 4 t'
       , Text.length ds == 4
       -> readDigits str ds t''

     _ -> Nothing

 readDigits str ds t =
    case readHex (Text.unpack ds) of
      (n, []):_ -> continue str (toEnum n) t
      _ -> Nothing

-- | This class exists so that solvers supporting the SMTLib2 format can support
--   features that go slightly beyond the standard.
--
-- In particular, there is no standardized syntax for constant arrays (arrays
-- which map every index to the same value).  Solvers that support the theory of
-- arrays and have custom syntax for constant arrays should implement
-- `smtlib2arrayConstant`.  In addition, solvers may override the default
-- representation of complex numbers if necessary.  The default is to represent
-- complex numbers as "(Array Bool Real)" and to build instances by updating a
-- constant array.
class Show a => SMTLib2Tweaks a where
  smtlib2tweaks :: a

  smtlib2exitCommand :: Maybe SMT2.Command
  smtlib2exitCommand = Just SMT2.exit

  -- | Return a representation of the type associated with a (multi-dimensional) symbolic
  -- array.
  --
  -- By default, we encode symbolic arrays using a nested representation.  If the solver,
  -- supports tuples/structs it may wish to change this.
  smtlib2arrayType :: [SMT2.Sort] -> SMT2.Sort -> SMT2.Sort
  smtlib2arrayType l r = foldr (\i v -> SMT2.arraySort i v) r l

  smtlib2arrayConstant :: Maybe ([SMT2.Sort] -> SMT2.Sort -> Term -> Term)
  smtlib2arrayConstant = Nothing

  smtlib2arraySelect :: Term -> [Term] -> Term
  smtlib2arraySelect a [] = a
  smtlib2arraySelect a (h:l) = smtlib2arraySelect @a (What4.Protocol.SMTLib2.arraySelect a h) l

  smtlib2arrayUpdate :: Term -> [Term] -> Term -> Term
  smtlib2arrayUpdate a i v =
    case i of
      [] -> error "arrayUpdate given empty list"
      i1:ir -> nestedArrayUpdate a (i1, ir) v

  smtlib2StringSort :: SMT2.Sort
  smtlib2StringSort = SMT2.Sort "String"

  smtlib2StringTerm :: Text -> Term
  smtlib2StringTerm = textToTerm

  smtlib2StringLength :: Term -> Term
  smtlib2StringLength = SMT2.un_app "str.len"

  smtlib2StringAppend :: [Term] -> Term
  smtlib2StringAppend = SMT2.term_app "str.++"

  smtlib2StringContains :: Term -> Term -> Term
  smtlib2StringContains = SMT2.bin_app "str.contains"

  smtlib2StringIndexOf :: Term -> Term -> Term -> Term
  smtlib2StringIndexOf s t i = SMT2.term_app "str.indexof" [s,t,i]

  smtlib2StringIsPrefixOf :: Term -> Term -> Term
  smtlib2StringIsPrefixOf = SMT2.bin_app "str.prefixof"

  smtlib2StringIsSuffixOf :: Term -> Term -> Term
  smtlib2StringIsSuffixOf = SMT2.bin_app "str.suffixof"

  smtlib2StringSubstring :: Term -> Term -> Term -> Term
  smtlib2StringSubstring x off len = SMT2.term_app "str.substr" [x,off,len]

  -- | The sort of structs with the given field types.
  --
  -- By default, this uses SMTLIB2 datatypes and are not primitive to the language.
  smtlib2StructSort :: [SMT2.Sort] -> SMT2.Sort
  smtlib2StructSort [] = SMT2.Sort "Struct0"
  smtlib2StructSort flds = SMT2.Sort $ "(Struct" <> Builder.decimal n <> foldMap f flds <> ")"
       where f :: SMT2.Sort -> Builder
             f (SMT2.Sort s) = " " <> s
             n = length flds

  -- | Construct a struct value from the given field values
  smtlib2StructCtor :: [Term] -> Term
  smtlib2StructCtor args = term_app nm args
    where nm = "mk-struct" <> Builder.decimal (length args)

  -- | Construct a struct field projection term
  smtlib2StructProj ::
    Int {- ^ number of fields in the struct -} ->
    Int {- ^ 0-based index of the struct field -} ->
    Term {- ^ struct term to project from -} ->
    Term
  smtlib2StructProj n i a = term_app nm [a]
    where nm = "struct" <> Builder.decimal n <> "-proj" <> Builder.decimal i

  -- By default, this uses the SMTLib 2.6 standard version of the declare-datatype command.
  smtlib2declareStructCmd :: Int -> Maybe SMT2.Command
  smtlib2declareStructCmd 0 = Just $
    SMT2.Cmd $ app "declare-datatype" [ fromString "Struct0", builder_list [ builder_list ["mk-struct0"]]]
  smtlib2declareStructCmd n = Just $
    let n_str = fromString (show n)
        tp = "Struct" <> n_str
        cnstr = "mk-struct" <> n_str
        idxes = map (fromString . show) [0 .. n-1]
        tp_names = [ "T" <> i_str
                   | i_str <- idxes
                   ]
        flds = [ app ("struct" <> n_str <> "-proj" <> i_str) [ "T" <> i_str ]
               | i_str <- idxes
               ]
     in SMT2.Cmd $ app "declare-datatype" [ tp, app "par" [ builder_list tp_names, builder_list [app cnstr flds]]]



asSMT2Type :: forall a tp . SMTLib2Tweaks a => TypeMap tp -> SMT2.Sort
asSMT2Type BoolTypeMap    = SMT2.boolSort
asSMT2Type IntegerTypeMap = SMT2.intSort
asSMT2Type RealTypeMap    = SMT2.realSort
asSMT2Type (BVTypeMap w)  = SMT2.bvSort (natValue w)
asSMT2Type (FloatTypeMap fpp) = SMT2.Sort $ mkFloatSymbol "FloatingPoint" (asSMTFloatPrecision fpp)
asSMT2Type UnicodeTypeMap = smtlib2StringSort @a
asSMT2Type ComplexToStructTypeMap =
  smtlib2StructSort @a [ SMT2.realSort, SMT2.realSort ]
asSMT2Type ComplexToArrayTypeMap =
  smtlib2arrayType @a [SMT2.boolSort] SMT2.realSort
asSMT2Type (PrimArrayTypeMap i r) =
  smtlib2arrayType @a (toListFC (asSMT2Type @a) i) (asSMT2Type @a r)
asSMT2Type (FnArrayTypeMap _ _) =
  error "SMTLIB backend does not support function types as first class."
asSMT2Type (StructTypeMap f) =
  smtlib2StructSort @a (toListFC (asSMT2Type @a) f)

-- Default instance.
instance SMTLib2Tweaks () where
  smtlib2tweaks = ()

------------------------------------------------------------------------
readBin :: Num a => ReadS a
readBin = readInt 2 (`elem` ("01" :: String)) digitToInt

------------------------------------------------------------------------
-- Type

mkRoundingOp :: Builder -> RoundingMode -> Builder
mkRoundingOp op r = op <> " " <> fromString (show r)

------------------------------------------------------------------------
-- Writer

newtype Writer a = Writer { declaredTuples :: IORef (Set Int) }

type instance SMTWriter.Term (Writer a) = Term

instance Num Term where
  x + y = SMT2.add [x, y]
  x - y = SMT2.sub x [y]
  x * y = SMT2.mul [x, y]
  negate x = SMT2.negate x
  abs x    = SMT2.ite (SMT2.ge [x, SMT2.numeral 0]) x (SMT2.negate x)
  signum x =
    SMT2.ite (SMT2.ge [x, SMT2.numeral 0])
             (SMT2.ite (SMT2.eq [x, SMT2.numeral 0]) (SMT2.numeral 0) (SMT2.numeral 1))
             (SMT2.negate (SMT2.numeral 1))
  fromInteger = SMT2.numeral

varBinding :: forall a . SMTLib2Tweaks a => (Text, Some TypeMap) -> (Text, SMT2.Sort)
varBinding (nm, Some tp) = (nm, asSMT2Type @a tp)

-- The SMTLIB2 exporter uses the datatypes theory for representing structures.
--
-- Note about structs:
--
-- For each length XX associated to some structure with that length in the
-- formula, the SMTLIB2 backend defines a datatype "StructXX" with the
-- constructor "mk-structXX", and projection operations "structXX-projII"
-- for II an natural number less than XX.
instance SupportTermOps Term where
  boolExpr b = if b then SMT2.true else SMT2.false
  notExpr = SMT2.not

  andAll = SMT2.and
  orAll  = SMT2.or

  x .== y = SMT2.eq [x,y]
  x ./= y = SMT2.distinct [x,y]

  -- NB: SMT2.letBinder defines a "parallel" let, and
  -- we want the semantics of a "sequential" let, so expand
  -- to a series of nested lets.
  letExpr vs t = foldr (\v -> SMT2.letBinder [v]) t vs

  ite = SMT2.ite

  sumExpr = SMT2.add

  termIntegerToReal = SMT2.toReal
  termRealToInteger = SMT2.toInt

  integerTerm = SMT2.numeral
  intDiv x y = SMT2.div x [y]
  intMod = SMT2.mod
  intAbs     = SMT2.abs

  intDivisible x 0 = x .== integerTerm 0
  intDivisible x k = intMod x (integerTerm (toInteger k)) .== 0

  rationalTerm r | d == 1    = SMT2.decimal n
                 | otherwise = (SMT2.decimal n) SMT2../ [SMT2.decimal d]
    where n = numerator r
          d = denominator r

  x .<  y = SMT2.lt [x,y]
  x .<= y = SMT2.le [x,y]
  x .>  y = SMT2.gt [x,y]
  x .>= y = SMT2.ge [x,y]

  bvTerm w u = case isZeroOrGT1 w of
    Left Refl -> error "Cannot construct BV term with 0 width"
    Right LeqProof -> SMT2.bvdecimal w u

  bvNeg = SMT2.bvneg
  bvAdd x y = SMT2.bvadd x [y]
  bvSub = SMT2.bvsub
  bvMul x y = SMT2.bvmul x [y]

  bvSLe = SMT2.bvsle
  bvULe = SMT2.bvule

  bvSLt = SMT2.bvslt
  bvULt = SMT2.bvult

  bvUDiv = SMT2.bvudiv
  bvURem = SMT2.bvurem
  bvSDiv = SMT2.bvsdiv
  bvSRem = SMT2.bvsrem

  bvNot = SMT2.bvnot
  bvAnd x y = SMT2.bvand x [y]
  bvOr  x y = SMT2.bvor  x [y]
  bvXor x y = SMT2.bvxor x [y]

  bvShl  = SMT2.bvshl
  bvLshr = SMT2.bvlshr
  bvAshr = SMT2.bvashr

  bvConcat = SMT2.concat

  bvExtract _ b n x | n > 0 = SMT2.extract (b+n-1) b x
                    | otherwise = error $ "bvExtract given non-positive width " ++ show n

  floatNeg  = un_app "fp.neg"
  floatAbs  = un_app "fp.abs"
  floatSqrt r = un_app $ mkRoundingOp "fp.sqrt " r

  floatAdd r = bin_app $ mkRoundingOp "fp.add" r
  floatSub r = bin_app $ mkRoundingOp "fp.sub" r
  floatMul r = bin_app $ mkRoundingOp "fp.mul" r
  floatDiv r = bin_app $ mkRoundingOp "fp.div" r
  floatRem = bin_app "fp.rem"

  floatFMA r x y z = term_app (mkRoundingOp "fp.fma" r) [x, y, z]

  floatEq x y  = SMT2.eq [x,y]
  floatFpEq = bin_app "fp.eq"
  floatLe   = bin_app "fp.leq"
  floatLt   = bin_app "fp.lt"

  floatIsNaN      = un_app "fp.isNaN"
  floatIsInf      = un_app "fp.isInfinite"
  floatIsZero     = un_app "fp.isZero"
  floatIsPos      = un_app "fp.isPositive"
  floatIsNeg      = un_app "fp.isNegative"
  floatIsSubnorm  = un_app "fp.isSubnormal"
  floatIsNorm     = un_app "fp.isNormal"

  floatTerm fpp@(FloatingPointPrecisionRepr eb sb) bf =
      un_app (mkFloatSymbol "to_fp" (asSMTFloatPrecision fpp)) (bvTerm w bv)
    where
      w = addNat eb sb
      bv = BV.mkBV w (bfToBits (fppOpts fpp RNE) bf)

  floatCast fpp r = un_app $ mkRoundingOp (mkFloatSymbol "to_fp" (asSMTFloatPrecision fpp)) r
  floatRound r = un_app $ mkRoundingOp "fp.roundToIntegral" r
  floatFromBinary fpp = un_app $ mkFloatSymbol "to_fp" (asSMTFloatPrecision fpp)
  bvToFloat fpp r =
    un_app $ mkRoundingOp (mkFloatSymbol "to_fp_unsigned" (asSMTFloatPrecision fpp)) r
  sbvToFloat fpp r = un_app $ mkRoundingOp (mkFloatSymbol "to_fp" (asSMTFloatPrecision fpp)) r
  realToFloat fpp r = un_app $ mkRoundingOp (mkFloatSymbol "to_fp" (asSMTFloatPrecision fpp)) r

  floatToBV w r =
    un_app $ mkRoundingOp ("(_ fp.to_ubv " <> fromString (show w) <> ")") r
  floatToSBV w r =
    un_app $ mkRoundingOp ("(_ fp.to_sbv " <> fromString (show w) <> ")") r

  floatToReal = un_app "fp.to_real"

  realIsInteger = SMT2.isInt

  realDiv x y = x SMT2../ [y]
  realSin = un_app "sin"
  realCos = un_app "cos"
  realTan = un_app "tan"
  realATan2 = bin_app "atan2"
  realSinh = un_app "sinh"
  realCosh = un_app "cosh"
  realTanh = un_app "tanh"
  realExp = un_app "exp"
  realLog = un_app "log"

  smtFnApp nm args = term_app (SMT2.renderTerm nm) args

  fromText t = SMT2.T (Builder.fromText t)

------------------------------------------------------------------------
-- Writer

newWriter :: a
          -> Streams.OutputStream Text
             -- ^ Stream to write queries onto
          -> Streams.InputStream Text
              -- ^ Input stream to read responses from
              --   (may be the @nullInput@ stream if no responses are expected)
          -> AcknowledgementAction t (Writer a)
             -- ^ Action to run for consuming acknowledgement messages
          -> ResponseStrictness
             -- ^ Be strict in parsing SMT solver responses?
          -> String
             -- ^ Name of solver for reporting purposes.
          -> Bool
             -- ^ Flag indicating if it is permitted to use
             -- "define-fun" when generating SMTLIB
          -> ProblemFeatures
             -- ^ Indicates what features are supported by the solver
          -> Bool
             -- ^ Indicates if quantifiers are supported.
          -> B.SymbolVarBimap t
             -- ^ Variable bindings for names.
          -> IO (WriterConn t (Writer a))
newWriter _ h in_h ack isStrict solver_name permitDefineFun arithOption quantSupport bindings = do
  r <- newIORef Set.empty
  let initWriter =
        Writer
        { declaredTuples = r
        }
  conn <- newWriterConn h in_h ack solver_name isStrict arithOption bindings initWriter
  return $! conn { supportFunctionDefs = permitDefineFun
                 , supportQuantifiers = quantSupport
                 }

type instance Command (Writer a) = SMT2.Command

instance SMTLib2Tweaks a => SMTWriter (Writer a) where
  forallExpr vars t = SMT2.forall_ (varBinding @a <$> vars) t
  existsExpr vars t = SMT2.exists_ (varBinding @a <$> vars) t

  arrayConstant =
    case smtlib2arrayConstant @a of
      Just f -> Just $ \idxTypes (Some retType) c ->
        f ((\(Some itp) -> asSMT2Type @a itp) <$> idxTypes) (asSMT2Type @a retType) c
      Nothing -> Nothing
  arraySelect = smtlib2arraySelect @a
  arrayUpdate = smtlib2arrayUpdate @a

  commentCommand _ b = SMT2.Cmd ("; " <> b)

  assertCommand _ e = SMT2.assert e

  assertNamedCommand _ e nm = SMT2.assertNamed e nm

  pushCommand _  = SMT2.push 1
  popCommand _   = SMT2.pop 1
  resetCommand _ = SMT2.resetAssertions
  popManyCommands _ n = [SMT2.pop (toInteger n)]

  checkCommands _ = [SMT2.checkSat]
  checkWithAssumptionsCommands _ nms = [SMT2.checkSatWithAssumptions nms]

  getUnsatAssumptionsCommand _ = SMT2.getUnsatAssumptions
  getUnsatCoreCommand _ = SMT2.getUnsatCore
  getAbductCommand _ nm e g = SMT2.getAbduct (Text.pack nm) e g
  getAbductNextCommand _ = SMT2.getAbductNext
  
  setOptCommand _ = SMT2.setOption

  declareCommand _proxy v argTypes retType =
    SMT2.declareFun v (toListFC (asSMT2Type @a) argTypes) (asSMT2Type @a retType)

  defineCommand _proxy f args return_type e =
    let resolveArg (var, Some tp) = (var, asSMT2Type @a tp)
     in SMT2.defineFun f (resolveArg <$> args) (asSMT2Type @a return_type) e

  stringTerm str = smtlib2StringTerm @a str
  stringLength x = smtlib2StringLength @a x
  stringAppend xs = smtlib2StringAppend @a xs
  stringContains x y = smtlib2StringContains @a x y
  stringIsPrefixOf x y = smtlib2StringIsPrefixOf @a x y
  stringIsSuffixOf x y = smtlib2StringIsSuffixOf @a x y
  stringIndexOf x y k = smtlib2StringIndexOf @a x y k
  stringSubstring x off len = smtlib2StringSubstring @a x off len

  structCtor _tps vals = smtlib2StructCtor @a vals

  structProj tps idx v =
    let n = Ctx.sizeInt (Ctx.size tps)
        i = Ctx.indexVal idx
     in smtlib2StructProj @a n i v

  resetDeclaredStructs conn = do
    let r = declaredTuples (connState conn)
    writeIORef r mempty

  declareStructDatatype conn flds = do
    let n = Ctx.sizeInt (Ctx.size flds)
    let r = declaredTuples (connState conn)
    s <- readIORef r
    when (Set.notMember n s) $ do
      case smtlib2declareStructCmd @a n of
        Nothing -> return ()
        Just cmd -> addCommand conn cmd
      writeIORef r $! Set.insert n s

  writeCommand conn (SMT2.Cmd cmd) =
    do let cmdout = Lazy.toStrict (Builder.toLazyText cmd)
       Streams.write (Just (cmdout <> "\n")) (connHandle conn)
       -- force a flush
       Streams.write (Just "") (connHandle conn)

-- | Write check sat command
writeCheckSat :: SMTLib2Tweaks a => WriterConn t (Writer a) -> IO ()
writeCheckSat w = addCommandNoAck w SMT2.checkSat

writeExit :: forall a t. SMTLib2Tweaks a => WriterConn t (Writer a) -> IO ()
writeExit w = mapM_ (addCommand w) (smtlib2exitCommand @a)

setLogic :: SMTLib2Tweaks a => WriterConn t (Writer a) -> SMT2.Logic -> IO ()
setLogic w l = addCommand w $ SMT2.setLogic l

setOption :: SMTLib2Tweaks a => WriterConn t (Writer a) -> Text -> Text -> IO ()
setOption w nm val = addCommand w $ SMT2.setOption nm val

getVersion :: SMTLib2Tweaks a => WriterConn t (Writer a) -> IO ()
getVersion w = writeCommand w $ SMT2.getVersion

getName :: SMTLib2Tweaks a => WriterConn t (Writer a) -> IO ()
getName w = writeCommand w $ SMT2.getName

-- | Set the produce models option (We typically want this)
setProduceModels :: SMTLib2Tweaks a => WriterConn t (Writer a) -> Bool -> IO ()
setProduceModels w b = addCommand w $ SMT2.setProduceModels b

writeGetValue :: SMTLib2Tweaks a => WriterConn t (Writer a) -> [Term] -> IO ()
writeGetValue w l = addCommandNoAck w $ SMT2.getValue l

writeGetAbduct :: SMTLib2Tweaks a => WriterConn t (Writer a) -> Text -> Term -> String -> IO ()
writeGetAbduct w nm p g = addCommandNoAck w $ SMT2.getAbduct nm p g

writeGetAbductNext :: SMTLib2Tweaks a => WriterConn t (Writer a) -> IO ()
writeGetAbductNext w = addCommandNoAck w SMT2.getAbductNext

parseBoolSolverValue :: MonadFail m => SExp -> m Bool
parseBoolSolverValue (SAtom "true")  = return True
parseBoolSolverValue (SAtom "false") = return False
parseBoolSolverValue s =
  do v <- parseBvSolverValue (knownNat @1) s
     return (if v == BV.zero knownNat then False else True)

parseRealSolverValue :: MonadFail m => SExp -> m Rational
parseRealSolverValue (SAtom v) | Just (r,"") <- readDecimal (Text.unpack v) =
  return r
parseRealSolverValue (SApp ["-", x]) = do
  negate <$> parseRealSolverValue x
parseRealSolverValue (SApp ["/", x , y]) = do
  (/) <$> parseRealSolverValue x
      <*> parseRealSolverValue y
parseRealSolverValue s = fail $ "Could not parse solver value: " ++ show s

-- | Parse a bitvector value returned by a solver. Most solvers give
-- results of the right size, but ABC always gives hex results without
-- leading zeros, so they may be larger or smaller than the actual size
-- of the variable.
parseBvSolverValue :: MonadFail m => NatRepr w -> SExp -> m (BV.BV w)
parseBvSolverValue w s
  | Pair w' bv <- parseBVLitHelper s = case w' `compareNat` w of
      NatLT zw -> return (BV.zext (addNat w' (addNat zw knownNat)) bv)
      NatEQ -> return bv
      NatGT _ -> return (BV.trunc w bv)

natBV :: Natural
      -- ^ width
      -> Integer
      -- ^ BV value
      -> Pair NatRepr BV.BV
natBV wNatural x = case mkNatRepr wNatural of
  Some w -> Pair w (BV.mkBV w x)

-- | Parse an s-expression and return a bitvector and its width
parseBVLitHelper :: SExp -> Pair NatRepr BV.BV
parseBVLitHelper (SAtom (Text.unpack -> ('#' : 'b' : n_str))) | [(n, "")] <- readBin n_str =
  natBV (fromIntegral (length n_str)) n
parseBVLitHelper (SAtom (Text.unpack -> ('#' : 'x' : n_str))) | [(n, "")] <- readHex n_str =
  natBV (fromIntegral (length n_str * 4)) n
parseBVLitHelper (SApp ["_", SAtom (Text.unpack -> ('b' : 'v' : n_str)), SAtom (Text.unpack -> w_str)])
  | [(n, "")] <- readDec n_str, [(w, "")] <- readDec w_str = natBV w n
-- BGS: Is this correct?
parseBVLitHelper _ = natBV 0 0

parseStringSolverValue :: MonadFail m => SExp -> m Text
parseStringSolverValue (SString t) | Just t' <- unescapeText t = return t'
parseStringSolverValue x = fail ("Could not parse string solver value:\n  " ++ show x)

parseFloatSolverValue :: MonadFail m => FloatPrecisionRepr fpp
                      -> SExp
                      -> m (BV.BV (FloatPrecisionBits fpp))
parseFloatSolverValue (FloatingPointPrecisionRepr eb sb) s = do
  ParsedFloatResult sgn eb' expt sb' sig <- parseFloatLitHelper s
  case (eb `testEquality` eb',
        sb `testEquality` ((knownNat @1) `addNat` sb')) of
    (Just Refl, Just Refl) -> do
      -- eb' + 1 ~ 1 + eb'
      Refl <- return $ plusComm eb' (knownNat @1)
      -- (eb' + 1) + sb' ~ eb' + (1 + sb')
      Refl <- return $ plusAssoc eb' (knownNat @1) sb'
      return bv
        where bv = BV.concat (addNat (knownNat @1) eb) sb' (BV.concat knownNat eb sgn expt) sig
    _ -> fail $ "Unexpected float precision: " <> show eb' <> ", " <> show sb'

data ParsedFloatResult = forall eb sb . ParsedFloatResult
  (BV.BV 1)    -- sign
  (NatRepr eb) -- exponent width
  (BV.BV eb)   -- exponent
  (NatRepr sb) -- significand bit width
  (BV.BV sb)   -- significand bit

parseFloatLitHelper :: MonadFail m => SExp -> m ParsedFloatResult
parseFloatLitHelper (SApp ["fp", sign_s, expt_s, scand_s])
  | Pair sign_w sign <- parseBVLitHelper sign_s
  , Just Refl <- sign_w `testEquality` (knownNat @1)
  , Pair eb expt <- parseBVLitHelper expt_s
  , Pair sb scand <- parseBVLitHelper scand_s
  = return $ ParsedFloatResult sign eb expt sb scand
parseFloatLitHelper
  s@(SApp ["_", SAtom (Text.unpack -> nm), SAtom (Text.unpack -> eb_s), SAtom (Text.unpack -> sb_s)])
  | [(eb_n, "")] <- readDec eb_s, [(sb_n, "")] <- readDec sb_s
  , Some eb <- mkNatRepr eb_n
  , Some sb <- mkNatRepr (sb_n-1)
  = case nm of
      "+oo"   -> return $ ParsedFloatResult (BV.zero knownNat) eb (BV.maxUnsigned eb) sb (BV.zero sb)
      "-oo"   -> return $ ParsedFloatResult (BV.one knownNat)  eb (BV.maxUnsigned eb) sb (BV.zero sb)
      "+zero" -> return $ ParsedFloatResult (BV.zero knownNat) eb (BV.zero eb)        sb (BV.zero sb)
      "-zero" -> return $ ParsedFloatResult (BV.one knownNat)  eb (BV.zero eb)        sb (BV.zero sb)
      "NaN"   -> return $ ParsedFloatResult (BV.zero knownNat) eb (BV.maxUnsigned eb) sb (BV.maxUnsigned sb)
      _       -> fail $ "Could not parse float solver value: " ++ show s
parseFloatLitHelper s = fail $ "Could not parse float solver value: " ++ show s

parseBvArraySolverValue :: (MonadFail m,
                            1 <= w,
                            1 <= v)
                        => NatRepr w
                        -> NatRepr v
                        -> SExp
                        -> m (Maybe (GroundArray (Ctx.SingleCtx (BaseBVType w)) (BaseBVType v)))
parseBvArraySolverValue _ v (SApp [SApp ["as", "const", _], c]) = do
  c' <- parseBvSolverValue v c
  return . Just $ ArrayConcrete c' Map.empty
parseBvArraySolverValue w v (SApp ["store", arr, idx, val]) = do
  arr' <- parseBvArraySolverValue w v arr
  case arr' of
    Just (ArrayConcrete base m) -> do
      idx' <- B.BVIndexLit w <$> parseBvSolverValue w idx
      val' <- parseBvSolverValue v val
      return . Just $ ArrayConcrete base (Map.insert (Ctx.empty Ctx.:> idx') val' m)
    _ -> return Nothing
parseBvArraySolverValue _ _ _ = return Nothing

------------------------------------------------------------------------
-- Session

-- | This is an interactive session with an SMT solver
data Session t a = Session
  { sessionWriter   :: !(WriterConn t (Writer a))
  , sessionResponse :: !(Streams.InputStream Text)
  }

-- | Get a value from a solver (must be called after checkSat)
runGetValue :: SMTLib2Tweaks a
            => Session t a
            -> Term
            -> IO SExp
runGetValue s e = do
  writeGetValue (sessionWriter s) [ e ]
  let valRsp = \case
        AckSuccessSExp (SApp [SApp [_, b]]) -> Just b
        _ -> Nothing
  getLimitedSolverResponse "get value" valRsp (sessionWriter s) (SMT2.getValue [e])



-- | runGetAbducts s nm p n, returns n formulas (as strings) the disjunction of which entails p (along with all
--   the assertions in the context)
runGetAbducts :: SMTLib2Tweaks a
             => Session t a
             -> Int
             -> String
             -> Term
             -> [(SMTType, [(String, [SMTType])])]
             -> IO [String]
runGetAbducts s n nm p g = do
  let nm_t = Text.pack nm
  let rest = n - 1
  let gs = cfgToString g
  writeGetAbduct (sessionWriter s) nm_t p gs
  replicateM_ rest $ writeGetAbductNext (sessionWriter s)
  let valRsp = \case
        -- SMT solver returns `(define-fun nm () Bool X)` where X is the abduct, we discard everything but the abduct
        AckSuccessSExp (SApp (_ : _ : _ : _ : abduct)) -> Just (tail $ init $ sExpToString (SApp abduct))
        _ -> Nothing
  -- get first abduct using the get-abduct command
  abd1 <- getLimitedSolverResponse "get abduct" valRsp (sessionWriter s) (SMT2.getAbduct nm_t p gs)
  -- get the rest of the abducts using the get-abduct-next command
  abdRest <- forM [1..rest] $ \_ -> getLimitedSolverResponse "get abduct next" valRsp (sessionWriter s) (SMT2.getAbduct nm_t p gs)
  return (abd1:abdRest)

-- | This function runs a check sat command
runCheckSat :: forall b t a.
               SMTLib2Tweaks b
            => Session t b
            -> (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) () -> IO a)
               -- ^ Function for evaluating model.
               -- The evaluation should be complete before
            -> IO a
runCheckSat s doEval =
  do let w = sessionWriter s
         r = sessionResponse s
     addCommands w (checkCommands w)
     res <- smtSatResult w w
     case res of
       Unsat x -> doEval (Unsat x)
       Unknown -> doEval Unknown
       Sat _ ->
         do evalFn <- smtExprGroundEvalFn w (smtEvalFuns w r)
            doEval (Sat (evalFn, Nothing))

instance SMTLib2Tweaks a => SMTReadWriter (Writer a) where
  smtEvalFuns w s = smtLibEvalFuns Session { sessionWriter = w
                                           , sessionResponse = s }

  smtSatResult p s =
    let satRsp = \case
          AckSat     -> Just $ Sat ()
          AckUnsat   -> Just $ Unsat ()
          AckUnknown -> Just Unknown
          _ -> Nothing
    in getLimitedSolverResponse "sat result" satRsp s
       (head $ reverse $ checkCommands p)

  smtUnsatAssumptionsResult p s =
    let unsatAssumpRsp = \case
         AckSuccessSExp (asNegAtomList -> Just as) -> Just as
         _ -> Nothing
        cmd = getUnsatAssumptionsCommand p
    in getLimitedSolverResponse "unsat assumptions" unsatAssumpRsp s cmd

  smtUnsatCoreResult p s =
    let unsatCoreRsp = \case
          AckSuccessSExp (asAtomList -> Just nms) -> Just nms
          _ -> Nothing
        cmd = getUnsatCoreCommand p
    in getLimitedSolverResponse "unsat core" unsatCoreRsp s cmd

  smtAbductResult p s nm t g =
    let abductRsp = \case
          AckSuccessSExp (SApp (_ : _ : _ : _ : abduct)) -> Just (tail $ init $ sExpToString (SApp abduct))
          _ -> Nothing
        cmd = getAbductCommand p nm t g
    in getLimitedSolverResponse "get abduct" abductRsp s cmd

  smtAbductNextResult p s =
    let abductRsp = \case
          AckSuccessSExp (SApp (_ : _ : _ : _ : abduct)) -> Just (tail $ init $ sExpToString (SApp abduct))
          _ -> Nothing
        cmd = getAbductNextCommand p
    in getLimitedSolverResponse "get abduct next" abductRsp s cmd


smtAckResult :: AcknowledgementAction t (Writer a)
smtAckResult = AckAction $ getLimitedSolverResponse "get ack" $ \case
                 AckSuccess -> Just ()
                 _ -> Nothing


smtLibEvalFuns ::
  forall t a. SMTLib2Tweaks a => Session t a -> SMTEvalFunctions (Writer a)
smtLibEvalFuns s = SMTEvalFunctions
                  { smtEvalBool = evalBool
                  , smtEvalBV = evalBV
                  , smtEvalReal = evalReal
                  , smtEvalFloat = evalFloat
                  , smtEvalBvArray = Just (SMTEvalBVArrayWrapper evalBvArray)
                  , smtEvalString = evalStr
                  }
  where
  evalBool tm = parseBoolSolverValue =<< runGetValue s tm
  evalReal tm = parseRealSolverValue =<< runGetValue s tm
  evalStr tm = parseStringSolverValue =<< runGetValue s tm

  evalBV :: NatRepr w -> Term -> IO (BV.BV w)
  evalBV w tm = parseBvSolverValue w =<< runGetValue s tm

  evalFloat :: FloatPrecisionRepr fpp -> Term -> IO (BV.BV (FloatPrecisionBits fpp))
  evalFloat fpp tm = parseFloatSolverValue fpp =<< runGetValue s tm

  evalBvArray :: SMTEvalBVArrayFn (Writer a) w v
  evalBvArray w v tm = parseBvArraySolverValue w v =<< runGetValue s tm


class (SMTLib2Tweaks a, Show a) => SMTLib2GenericSolver a where
  defaultSolverPath :: a -> B.ExprBuilder t st fs -> IO FilePath

  defaultSolverArgs :: a -> B.ExprBuilder t st fs -> IO [String]

  defaultFeatures :: a -> ProblemFeatures

  getErrorBehavior :: a -> WriterConn t (Writer a) -> IO ErrorBehavior
  getErrorBehavior _ _ = return ImmediateExit

  supportsResetAssertions :: a -> Bool
  supportsResetAssertions _ = False

  setDefaultLogicAndOptions :: WriterConn t (Writer a) -> IO()

  newDefaultWriter
    :: a ->
       AcknowledgementAction t (Writer a) ->
       ProblemFeatures ->
       -- | strictness override configuration
       Maybe (CFG.ConfigOption I.BaseBoolType) ->
       B.ExprBuilder t st fs ->
       Streams.OutputStream Text ->
       Streams.InputStream Text ->
       IO (WriterConn t (Writer a))
  newDefaultWriter solver ack feats strictOpt sym h in_h = do
    let cfg = I.getConfiguration sym
    strictness <- parserStrictness strictOpt strictSMTParsing cfg
    newWriter solver h in_h ack strictness (show solver) True feats True
      =<< B.getSymbolVarBimap sym

  -- | Run the solver in a session.
  withSolver
    :: a
    -> AcknowledgementAction t (Writer a)
    -> ProblemFeatures
    -> Maybe (CFG.ConfigOption I.BaseBoolType)
       -- ^ strictness override configuration
    -> B.ExprBuilder t st fs
    -> FilePath
      -- ^ Path to solver executable
    -> LogData
    -> (Session t a -> IO b)
      -- ^ Action to run
    -> IO b
  withSolver solver ack feats strictOpt sym path logData action = do
    args <- defaultSolverArgs solver sym
    withProcessHandles path args Nothing $
      \hdls@(in_h, out_h, err_h, _ph) -> do

        (in_stream, out_stream, err_reader) <-
          demuxProcessHandles in_h out_h err_h
            (fmap (\x -> ("; ", x)) $ logHandle logData)

        writer <- newDefaultWriter solver ack feats strictOpt sym in_stream out_stream
        let s = Session
              { sessionWriter   = writer
              , sessionResponse = out_stream
              }

        -- Set solver logic and solver-specific options
        setDefaultLogicAndOptions writer

        -- Run action with session.
        r <- action s
        -- Tell solver to exit
        writeExit writer

        stopHandleReader err_reader

        ec <- cleanupProcess hdls
        case ec of
          Exit.ExitSuccess -> return r
          Exit.ExitFailure exit_code -> fail $
            show solver ++ " exited with unexpected code: " ++ show exit_code

  runSolverInOverride
    :: a
    -> AcknowledgementAction t (Writer a)
    -> ProblemFeatures
    -> Maybe (CFG.ConfigOption I.BaseBoolType)
    -- ^ strictness override configuration
    -> B.ExprBuilder t st fs
    -> LogData
    -> [B.BoolExpr t]
    -> (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) () -> IO b)
    -> IO b
  runSolverInOverride solver ack feats strictOpt sym logData predicates cont = do
    I.logSolverEvent sym
      (I.SolverStartSATQuery $ I.SolverStartSATQueryRec
        { I.satQuerySolverName = show solver
        , I.satQueryReason     = logReason logData
        })
    path <- defaultSolverPath solver sym
    withSolver solver ack feats strictOpt sym path (logData{logVerbosity=2}) $ \session -> do
      -- Assume the predicates hold.
      forM_ predicates (SMTWriter.assume (sessionWriter session))
      -- Run check SAT and get the model back.
      runCheckSat session $ \result -> do
        I.logSolverEvent sym
          (I.SolverEndSATQuery $ I.SolverEndSATQueryRec
            { I.satQueryResult = forgetModelAndCore result
            , I.satQueryError  = Nothing
            })
        cont result

-- | A default method for writing SMTLib2 problems without any
--   solver-specific tweaks.
writeDefaultSMT2 :: SMTLib2Tweaks a
                 => a
                 -> String
                    -- ^ Name of solver for reporting.
                 -> ProblemFeatures
                    -- ^ Features supported by solver
                 -> Maybe (CFG.ConfigOption I.BaseBoolType)
                    -- ^ strictness override configuration
                 -> B.ExprBuilder t st fs
                 -> IO.Handle
                 -> [B.BoolExpr t]
                 -> IO ()
writeDefaultSMT2 a nm feat strictOpt sym h ps = do
  bindings <- B.getSymbolVarBimap sym
  str <- Streams.encodeUtf8 =<< Streams.handleToOutputStream h
  null_in <- Streams.nullInput
  let cfg = I.getConfiguration sym
  strictness <- parserStrictness strictOpt strictSMTParsing cfg
  c <- newWriter a str null_in nullAcknowledgementAction strictness nm True feat True bindings
  setProduceModels c True
  forM_ ps (SMTWriter.assume c)
  writeCheckSat c
  writeExit c

-- n.b. commonly used for the startSolverProcess method of the
-- OnlineSolver class, so it's helpful for the type suffixes to align
startSolver
  :: SMTLib2GenericSolver a
  => a
  -> AcknowledgementAction t (Writer a)
        -- ^ Action for acknowledging command responses
  -> (WriterConn t (Writer a) -> IO ()) -- ^ Action for setting start-up-time options and logic
  -> SolverGoalTimeout
  -> ProblemFeatures
  -> Maybe (CFG.ConfigOption I.BaseBoolType)
  -- ^ strictness override configuration
  -> Maybe IO.Handle
  -> B.ExprBuilder t st fs
  -> IO (SolverProcess t (Writer a))
startSolver solver ack setup tmout feats strictOpt auxOutput sym = do
  path <- defaultSolverPath solver sym
  args <- defaultSolverArgs solver sym
  hdls@(in_h, out_h, err_h, ph) <- startProcess path args Nothing

  (in_stream, out_stream, err_reader) <-
     demuxProcessHandles in_h out_h err_h
       (fmap (\x -> ("; ", x)) auxOutput)

  -- Create writer
  writer <- newDefaultWriter solver ack feats strictOpt sym in_stream out_stream

  -- Set solver logic and solver-specific options
  setup writer

  -- Query the solver for it's error behavior
  errBeh <- getErrorBehavior solver writer

  earlyUnsatRef <- newIORef Nothing

  -- push an initial frame for solvers that don't support reset
  unless (supportsResetAssertions solver) (addCommand writer (SMT2.push 1))

  return $! SolverProcess
            { solverConn     = writer
            , solverCleanupCallback = cleanupProcess hdls
            , solverStderr   = err_reader
            , solverHandle   = ph
            , solverErrorBehavior = errBeh
            , solverEvalFuns = smtEvalFuns writer out_stream
            , solverLogFn    = I.logSolverEvent sym
            , solverName     = show solver
            , solverEarlyUnsat = earlyUnsatRef
            , solverSupportsResetAssertions = supportsResetAssertions solver
            , solverGoalTimeout = tmout
            }

shutdownSolver
  :: SMTLib2GenericSolver a => a -> SolverProcess t (Writer a) -> IO (Exit.ExitCode, Lazy.Text)
shutdownSolver _solver p = do
  -- Tell solver to exit
  writeExit (solverConn p)
  txt <- readAllLines (solverStderr p)
  stopHandleReader (solverStderr p)
  ec <- solverCleanupCallback p
  return (ec,txt)


-----------------------------------------------------------------
-- Checking solver version bounds


-- | Solver version bounds computed from \"solverBounds.config\"
defaultSolverBounds :: Map Text SolverBounds
defaultSolverBounds = Map.fromList $(computeDefaultSolverBounds)

-- | Things that can go wrong while checking which solver version we've got
data SolverVersionCheckError =
  UnparseableVersion Versions.ParsingError

ppSolverVersionCheckError :: SolverVersionCheckError -> PP.Doc ann
ppSolverVersionCheckError err =
  PP.vsep
  [ "Unexpected error while checking solver version:"
  , case err of
      UnparseableVersion parseErr ->
        PP.hsep
        [ "Couldn't parse solver version number:"
        , PP.viaShow parseErr
        ]
  ]

data SolverVersionError =
  SolverVersionError
  { vBounds :: SolverBounds
  , vActual :: Version
  }

ppSolverVersionError :: SolverVersionError -> PP.Doc ann
ppSolverVersionError err =
  PP.vsep
  [ "Solver did not meet version bound restrictions:"
  , "Lower bound (inclusive):" PP.<+> na (lower (vBounds err))
  , "Upper bound (non-inclusive):" PP.<+> na (upper (vBounds err))
  , "Actual version:" PP.<+> PP.viaShow (vActual err)
  ]
  where na (Just s) = PP.viaShow s
        na Nothing  = "n/a"

-- | Get the result of a version query
nameResult :: WriterConn t a -> IO Text
nameResult conn =
  getLimitedSolverResponse "solver name"
  (\case
      RspName nm -> Just nm
      _ -> Nothing
  )
  conn SMT2.getName


-- | Query the solver's error behavior setting
queryErrorBehavior :: SMTLib2Tweaks a =>
  WriterConn t (Writer a) -> IO ErrorBehavior
queryErrorBehavior conn =
  do let cmd = SMT2.getErrorBehavior
     writeCommand conn cmd
     getLimitedSolverResponse "error behavior"
       (\case
           RspErrBehavior bh -> case bh of
             "continued-execution" -> return ContinueOnError
             "immediate-exit" -> return ImmediateExit
             _ -> throw $ SMTLib2ResponseUnrecognized cmd bh
           _ -> Nothing
       ) conn cmd


-- | Get the result of a version query
versionResult :: WriterConn t a -> IO Text
versionResult conn =
  getLimitedSolverResponse "solver version"
  (\case
      RspVersion v -> Just v
      _ -> Nothing
  )
  conn SMT2.getVersion


-- | Ensure the solver's version falls within a known-good range.
checkSolverVersion' :: SMTLib2Tweaks solver =>
  Map Text SolverBounds ->
  SolverProcess scope (Writer solver) ->
  IO (Either SolverVersionCheckError (Maybe SolverVersionError))
checkSolverVersion' boundsMap proc =
  let conn = solverConn proc
      name = smtWriterName conn
      done = pure (Right Nothing)
      verr bnds actual = pure (Right (Just (SolverVersionError bnds actual))) in
  case Map.lookup (Text.pack name) boundsMap of
    Nothing -> done
    Just bnds ->
      do getVersion conn
         res <- versionResult $ solverConn proc
         case Versions.version res of
           Left e -> pure (Left (UnparseableVersion e))
           Right actualVer ->
             case (lower bnds, upper bnds) of
               (Nothing, Nothing) -> done
               (Nothing, Just maxVer) ->
                 if actualVer < maxVer then done else verr bnds actualVer
               (Just minVer, Nothing) ->
                 if minVer <= actualVer then done else verr bnds actualVer
               (Just minVer, Just maxVer) ->
                 if minVer <= actualVer && actualVer < maxVer then done else verr bnds actualVer


-- | Ensure the solver's version falls within a known-good range.
checkSolverVersion :: SMTLib2Tweaks solver =>
  SolverProcess scope (Writer solver) ->
  IO (Either SolverVersionCheckError (Maybe SolverVersionError))
checkSolverVersion = checkSolverVersion' defaultSolverBounds

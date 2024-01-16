{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PatternSynonyms #-}

module What4.Serialize.Printer
  (
    serializeExpr
  , serializeExprWithConfig
  , serializeSymFn
  , serializeSymFnWithConfig
  , serializeBaseType
  , convertBaseTypes
  , Config(..)
  , Result(..)
  , printSExpr
  , defaultConfig
  , SExpr
  , Atom(..)
  , SomeExprSymFn(..)
  , S.WellFormedSExpr(..)
  , ident, int, string
  , bitvec, bool, nat, real
  , ppFreeVarEnv
  , ppFreeSymFnEnv
  , pattern S.L
  , pattern S.A
  ) where

import           Numeric.Natural
import qualified Data.Foldable as F
import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.Map.Ordered (OMap)
import qualified Data.Map.Ordered as OMap
import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Some
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Parameterized.Nonce as Nonce
import qualified Data.Parameterized.TraversableFC as FC

import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import           Data.Word ( Word64 )
import qualified Control.Monad as M
import           Control.Monad.State.Strict (State)
import qualified Control.Monad.State.Strict as MS

import qualified Data.SCargot.Repr.WellFormed as S

import           What4.BaseTypes
import qualified What4.Expr as W4
import qualified What4.Expr.ArrayUpdateMap as WAU
import qualified What4.Expr.BoolMap as BooM
import qualified What4.Expr.Builder as W4
import qualified What4.Expr.WeightedSum as WSum
import qualified What4.IndexLit as WIL
import qualified What4.Interface as W4
import qualified What4.Symbol as W4
import qualified What4.Utils.StringLiteral as W4S


import           What4.Serialize.SETokens ( Atom(..), printSExpr
                                          , ident, int, nat, string
                                          , bitvec, bool, real, float
                                          )

type SExpr = S.WellFormedSExpr Atom

data SomeExprSymFn t = forall dom ret. SomeExprSymFn (W4.ExprSymFn t dom ret)

instance Eq (SomeExprSymFn t) where
  (SomeExprSymFn fn1) == (SomeExprSymFn fn2) =
    case W4.testEquality (W4.symFnId fn1) (W4.symFnId fn2) of
      Just _ -> True
      _ -> False

instance Ord (SomeExprSymFn t) where
  compare (SomeExprSymFn fn1) (SomeExprSymFn fn2) =
    compare (Nonce.indexValue $ W4.symFnId fn1) (Nonce.indexValue $ W4.symFnId fn2)


instance Show (SomeExprSymFn t) where
  show (SomeExprSymFn f) = show f


type VarNameEnv t = OMap (Some (W4.ExprBoundVar t)) Text
type FnNameEnv t  = OMap (SomeExprSymFn t) Text

ppFreeVarEnv :: VarNameEnv t -> String
ppFreeVarEnv env = show $ map toStr entries
  where entries = OMap.toAscList env
        toStr :: ((Some (W4.ExprBoundVar t)), Text) -> (String, String, String)
        toStr ((Some var), newName) = ( T.unpack $ W4.solverSymbolAsText $ W4.bvarName var
                                      , show $ W4.bvarType var
                                      , T.unpack newName
                                      )

ppFreeSymFnEnv :: FnNameEnv t -> String
ppFreeSymFnEnv env = show $ map toStr entries
  where entries = OMap.toAscList env
        toStr :: ((SomeExprSymFn t), Text) -> (String, String, String)
        toStr ((SomeExprSymFn fn), newName) = ( T.unpack $ W4.solverSymbolAsText $ W4.symFnName fn
                                              , show $ W4.symFnArgTypes fn
                                              , T.unpack newName
                                              )

-- | Controls how expressions and functions are serialized.
data Config =
  Config
  { cfgAllowFreeVars :: Bool
  -- ^ When @True@, any free What4 @ExprBoundVar@
  -- encountered is simply serialized with a unique name,
  -- and the mapping from What4 ExprBoundVar to unique names
  -- is returned after serialization. When False, an error
  -- is raised when a "free" @ExprBoundVar@ is encountered.
  , cfgAllowFreeSymFns :: Bool
  -- ^ When @True@, any encountered What4 @ExprSymFn@ during
  -- serialization is simply assigned a unique name and the
  -- mapping from What4 ExprSymFn to unique name is returned
  -- after serialization. When @False, encountered
  -- ExprSymFns are serialized at the top level of the
  -- expression in a `(letfn ([f ...]) ...)`.
  }

data Result t =
  Result
  { resSExpr :: S.WellFormedSExpr Atom
  -- ^ The serialized term.
  , resFreeVarEnv :: VarNameEnv t
  -- ^ The free BoundVars that were encountered during
  -- serialization and their associated fresh name
  -- that was used to generate the s-expression.
  , resSymFnEnv :: FnNameEnv t
  -- ^ The SymFns that were encountered during serialization
  -- and their associated fresh name that was used to
  -- generate the s-expression.
  }


defaultConfig :: Config
defaultConfig = Config { cfgAllowFreeVars = False, cfgAllowFreeSymFns = False}

-- This file is organized top-down, i.e., from high-level to low-level.

-- | Serialize a What4 Expr as a well-formed s-expression
-- (i.e., one which contains no improper lists). Equivalent
-- to @(resSExpr (serializeExpr' defaultConfig))@. Sharing
-- in the AST is achieved via a top-level let-binding around
-- the emitted expression (unless there are no terms with
-- non-atomic terms which can be shared).
serializeExpr :: W4.Expr t tp -> SExpr
serializeExpr = resSExpr . (serializeExprWithConfig defaultConfig)

-- | Serialize a What4 Expr as a well-formed s-expression
-- (i.e., one which contains no improper lists) according to
-- the configuration. Sharing in the AST is achieved via a
-- top-level let-binding around the emitted expression
-- (unless there are no terms with non-atomic terms which
-- can be shared).
serializeExprWithConfig :: Config -> W4.Expr t tp -> Result t
serializeExprWithConfig cfg expr = serializeSomething cfg (convertExprWithLet expr)

-- | Serialize a What4 ExprSymFn as a well-formed
-- s-expression (i.e., one which contains no improper
-- lists). Equivalent to @(resSExpr (serializeSymFn'
-- defaultConfig))@. Sharing in the AST is achieved via a
-- top-level let-binding around the emitted expression
-- (unless there are no terms with non-atomic terms which
-- can be shared).
serializeSymFn :: W4.ExprSymFn t dom ret -> SExpr
serializeSymFn = resSExpr . (serializeSymFnWithConfig defaultConfig)


-- | Serialize a What4 ExprSymFn as a well-formed
-- s-expression (i.e., one which contains no improper lists)
-- according to the configuration. Sharing in the AST is
-- achieved via a top-level let-binding around the emitted
-- expression (unless there are no terms with non-atomic
-- terms which can be shared).
serializeSymFnWithConfig :: Config -> W4.ExprSymFn t dom ret -> Result t
serializeSymFnWithConfig cfg fn = serializeSomething cfg (convertSymFn fn)

-- | Run the given Memo computation to produce a well-formed
-- s-expression (i.e., one which contains no improper lists)
-- according to the configuration. Sharing in the AST is
-- achieved via a top-level let-binding around the emitted
-- expression (unless there are no terms with non-atomic
-- terms which can be shared).
serializeSomething :: Config -> Memo t SExpr -> Result t
serializeSomething cfg something =
  let (maybeLetFn, getFreeSymFnEnv) = if cfgAllowFreeSymFns cfg
                                      then (return, envFreeSymFnEnv)
                                      else (letFn, \_ -> OMap.empty)
      (sexpr, menv) = runMemo cfg $ something >>= maybeLetFn
      letBindings = map (\(varName, boundExpr) -> S.L [ ident varName, boundExpr ])
                    $ map snd
                    $ OMap.assocs
                    $ envLetBindings menv
      res = mkLet letBindings sexpr
    in Result { resSExpr = res
              , resFreeVarEnv = envFreeVarEnv menv
              , resSymFnEnv = getFreeSymFnEnv menv
              }


serializeBaseType :: BaseTypeRepr tp -> SExpr
serializeBaseType bt = convertBaseType bt

data MemoEnv t =
  MemoEnv
  { envConfig :: !Config
  -- ^ User provided configuration for serialization.
  , envIdCounter :: !Natural
  -- ^ Internal counter for generating fresh names
  , envLetBindings :: !(OMap SKey (Text, SExpr))
  -- ^ Mapping from What4 expression nonces to the
  -- corresponding let-variable name (the @fst@) and the
  -- corresponding bound term (the @snd@).
  , envFreeVarEnv :: !(VarNameEnv t)
  -- ^ Mapping from What4 ExprBoundVar to the fresh names
  -- assigned to them for serialization purposes.
  , envFreeSymFnEnv :: !(FnNameEnv t)
  -- ^ Mapping from What4 ExprSymFn to the fresh names
  -- assigned to them for serialization purposes.
  , envBoundVars :: Set (Some (W4.ExprBoundVar t))
  -- ^ Set of currently in-scope What4 ExprBoundVars (i.e.,
  -- ExprBoundVars for whom we are serializing the body of
  -- their binding form).
  }

initEnv :: forall t . Config -> MemoEnv t
initEnv cfg = MemoEnv { envConfig = cfg
                      , envIdCounter = 0
                      , envLetBindings = OMap.empty
                      , envFreeVarEnv = OMap.empty
                      , envFreeSymFnEnv = OMap.empty
                      , envBoundVars = Set.empty
                      }

type Memo t a = State (MemoEnv t) a

runMemo :: Config -> (Memo t a) -> (a, MemoEnv t)
runMemo cfg m = MS.runState m $ initEnv cfg


-- | Serialize the given sexpression within a @letfn@ which
-- serializes and binds all of the encountered SymFns. Note:
-- this recursively also discovers and then serializes
-- SymFns referenced within the body of the SymFns
-- encountered thus far.
letFn :: SExpr -> Memo t SExpr
letFn sexpr = go [] [] Set.empty
  where
    go :: [((SomeExprSymFn t), Text)] -> [(Text, SExpr)] -> Set Text ->  Memo t SExpr
    go [] fnBindings seen = do
      -- Although the `todo` list is empty, we may have
      -- encountered some SymFns along the way, so check for
      -- those and serialize any previously unseen SymFns.
      newFns <- MS.gets (filter (\(_symFn, varName) -> not $ Set.member varName seen)
                         . OMap.assocs
                         . envFreeSymFnEnv)
      if null newFns
        then if null fnBindings
             then return sexpr
             else let bs = map (\(name, def) -> S.L [ident name, def]) fnBindings
                  in return $ S.L [ident "letfn" , S.L bs, sexpr]
        else go newFns fnBindings seen
    go (((SomeExprSymFn nextFn), nextFnName):todo) fnBindings seen = do
      nextSExpr <- convertSymFn nextFn
      let fnBindings' = (nextFnName, nextSExpr):fnBindings
          seen' = Set.insert nextFnName seen
      go todo fnBindings' seen'


-- | Converts the given What4 expression into an
-- s-expression and clears the let-binding cache (since it
-- just emitted a let binding with any necessary let-bound
-- vars).
convertExprWithLet :: W4.Expr t tp -> Memo t SExpr
convertExprWithLet expr = do
  b <- convertExpr expr
  bs <- map (\(varName, boundExpr) -> S.L [ ident varName, boundExpr ])
        <$> map snd
        <$> OMap.assocs
        <$> MS.gets envLetBindings
  MS.modify' (\r -> r {envLetBindings = OMap.empty})
  return $ mkLet bs b

mkLet :: [SExpr] -> SExpr -> SExpr
mkLet [] body       = body
mkLet bindings body = S.L [ident "let", S.L bindings, body]


-- | Converts a What4 ExprSymFn into an s-expression within
-- the Memo monad (i.e., no @let@ or @letfn@s are emitted).
convertSymFn :: forall t args ret
              . W4.ExprSymFn t args ret
             -> Memo t SExpr
convertSymFn symFn@(W4.ExprSymFn _ symFnName symFnInfo _) = do
 case symFnInfo of
   W4.DefinedFnInfo argVars body _ -> do
     let sArgTs = convertBaseTypes (W4.fnArgTypes symFn)
         sRetT = convertBaseType (W4.fnReturnType symFn)
     argsWithFreshNames <- let rawArgs = FC.toListFC Some argVars
                           in mapM getBoundVarWithFreshName rawArgs
     let (origBoundVars, freshArgNames) = unzip argsWithFreshNames
     -- Convert the body with the bound variable set and
     -- free-variable mapping extended to reflect being
     -- under the function's binders.
     sExpr <- MS.withState (\ms -> let boundVars = envBoundVars ms
                                       fvEnv = envFreeVarEnv ms
                             in ms { envBoundVars = Set.union boundVars (Set.fromList origBoundVars)
                                   , envFreeVarEnv = fvEnv OMap.<>| (OMap.fromList argsWithFreshNames)})
              $ convertExprWithLet body
     return $ S.L [ ident "definedfn"
                  , string (Some W4.UnicodeRepr) $ W4.solverSymbolAsText symFnName
                  , S.L ((ident "->"):sArgTs ++ [sRetT])
                  , S.L $ map ident freshArgNames
                  , sExpr
                  ]
   W4.UninterpFnInfo argTs retT ->
     let sArgTs = convertBaseTypes argTs
         sRetT = convertBaseType retT
     in return $ S.L [ ident "uninterpfn"
                     , string (Some W4.UnicodeRepr) $ W4.solverSymbolAsText symFnName
                     , S.L ((ident "->"):sArgTs ++ [sRetT])
                     ]
   W4.MatlabSolverFnInfo _msfn _argTs _body ->
     error "MatlabSolverFnInfo SymFns are not yet supported"
  where
    getBoundVarWithFreshName ::
      (Some (W4.ExprBoundVar t)) ->
      Memo t (Some (W4.ExprBoundVar t), Text)
    getBoundVarWithFreshName someVar@(Some var) = do
      nm <- freshName (W4.bvarType var)
      return (someVar, nm)


-- | Key for sharing SExpr construction. Internally indexes are expression nonces,
-- but the let-binding identifiers are based on insertion order to the OMap
newtype SKey = SKey {sKeyValue :: Word64}
  deriving (Eq, Ord, Show)



freshName :: W4.BaseTypeRepr tp -> Memo t Text
freshName tp = do
  idCount <- MS.gets envIdCounter
  MS.modify' $ (\e -> e {envIdCounter = idCount + 1})
  let prefix = case tp of
                 W4.BaseBoolRepr{} -> "bool"
                 W4.BaseIntegerRepr{} -> "int"
                 W4.BaseRealRepr{} -> "real"
                 W4.BaseFloatRepr{} -> "fl"
                 W4.BaseStringRepr{} -> "str"
                 W4.BaseComplexRepr -> "cmplx"
                 W4.BaseBVRepr{} -> "bv"
                 W4.BaseStructRepr{} -> "struct"
                 W4.BaseArrayRepr{} -> "arr"
                 W4.BaseVariantRepr{} -> "variant"
  return $ T.pack $ prefix++(show $ idCount)

freshFnName :: W4.ExprSymFn t args ret -> Memo t Text
freshFnName fn = do
  idCount <- MS.gets envIdCounter
  MS.modify' $ (\e -> e {envIdCounter = idCount + 1})
  let prefix = case W4.symFnInfo fn of
                 W4.UninterpFnInfo{} -> "ufn"
                 W4.DefinedFnInfo{} -> "dfn"
                 W4.MatlabSolverFnInfo{} -> "mfn"
  return $ T.pack $ prefix++(show $ idCount)



exprSKey :: W4.Expr t tp -> Maybe SKey
exprSKey x = SKey . Nonce.indexValue <$> W4.exprMaybeId x

-- | Allocate a fresh variable for the given
-- nonce-key/s-expression and save the variable/expression
-- mapping in the Memo monad.
addLetBinding :: SKey -> SExpr -> W4.BaseTypeRepr tp -> Memo t Text
addLetBinding key sexp tp = do
  letVarName <- freshName tp
  curLetBindings <- MS.gets envLetBindings
  MS.modify' $ (\e -> e {envLetBindings =  curLetBindings OMap.|> (key, (letVarName, sexp))})
  return letVarName

-- | Converts a What 4 expression into an s-expression
-- within the Memo monad (i.e., no @let@ or @letfn@s are
-- emitted in the result).
convertExpr :: forall t tp . W4.Expr t tp -> Memo t SExpr
convertExpr initialExpr = do
  case exprSKey initialExpr of
    Nothing -> go initialExpr
    Just key -> do
      letCache <- MS.gets envLetBindings
      case OMap.lookup key letCache of
        Just (name, _) -> return $ ident name
        Nothing -> do
          sexp <- go initialExpr
          case sexp of
            S.A _ -> return sexp -- Don't memoize atomic s-expressions - that's just silly.
            _ -> do
              letVarName <- addLetBinding key sexp (W4.exprType initialExpr)
              return $ ident letVarName
  where go :: W4.Expr t tp -> Memo t SExpr
        go (W4.SemiRingLiteral W4.SemiRingIntegerRepr val _) = return $ int val -- do we need/want these?
        go (W4.SemiRingLiteral W4.SemiRingRealRepr val _) = return $ real val
        go (W4.SemiRingLiteral (W4.SemiRingBVRepr _ sz) val _) = return $ bitvec (natValue sz) (BV.asUnsigned val)
        go (W4.StringExpr str _) =
          case (W4.stringLiteralInfo str) of
            W4.UnicodeRepr -> return $ string (Some W4.UnicodeRepr) (W4S.fromUnicodeLit str)
            W4.Char8Repr -> return $ string (Some W4.Char8Repr) $ T.decodeUtf8 $ W4S.fromChar8Lit str
            W4.Char16Repr -> error "Char16 strings are not yet supported"
              -- TODO - there is no `W4S.toLEByteString` currently... hmm...
              -- return $ string (Some W4.Char16Repr) $ T.decodeUtf16LE $ W4S.toLEByteString $ W4S.fromChar16Lit str
        go (W4.FloatExpr prec bf _) = return $ float prec bf
        go (W4.BoolExpr b _) = return $ bool b
        go (W4.AppExpr appExpr) = convertAppExpr' appExpr
        go (W4.NonceAppExpr nae) =
          case W4.nonceExprApp nae of
            W4.FnApp fn args -> convertFnApp fn args
            W4.Forall {} -> error "Forall NonceAppExpr not yet supported"
            W4.Exists {} -> error "Exists NonceAppExpr not yet supported"
            W4.ArrayFromFn {} -> error "ArrayFromFn NonceAppExpr not yet supported"
            W4.MapOverArrays {} -> error "MapOverArrays NonceAppExpr not yet supported"
            W4.ArrayTrueOnEntries {} -> error "ArrayTrueOnEntries NonceAppExpr not yet supported"
            W4.Annotation {} -> error "Annotation NonceAppExpr not yet supported"
        go (W4.BoundVarExpr var) = convertBoundVarExpr var

-- | Serialize bound variables as the s-expression identifier `name_nonce`. This allows us to
-- preserve their human-readable name while ensuring they are globally unique w/ the nonce suffix.
convertBoundVarExpr :: forall t tp. W4.ExprBoundVar t tp -> Memo t SExpr
convertBoundVarExpr x = do
  fvsAllowed <- MS.gets (cfgAllowFreeVars . envConfig)
  bvs <- MS.gets envBoundVars
  -- If this variable is not bound (in the standard syntactic sense)
  -- and free variables are not explicitly permitted, raise an error.
  M.when ((not $ Set.member (Some x) bvs) && (not fvsAllowed)) $
    error $
    "encountered the free What4 ExprBoundVar `"
    ++ (T.unpack (W4.solverSymbolAsText (W4.bvarName x)))
    ++ "`, but the user-specified configuration dissallows free variables."
  -- Get the renaming cache and either use the name already generated
  -- or generate a fresh name and record it.
  varEnv <- MS.gets envFreeVarEnv
  case OMap.lookup (Some x) varEnv of
    Just var -> return $ ident var
    Nothing -> do
      varName <- freshName $ W4.bvarType x
      MS.modify' $ (\e -> e {envFreeVarEnv = varEnv OMap.|> ((Some x), varName)})
      return $ ident varName


convertAppExpr' :: forall t tp . W4.AppExpr t tp -> Memo t SExpr
convertAppExpr' = go . W4.appExprApp
  where go :: forall tp' . W4.App (W4.Expr t) tp' -> Memo t SExpr
        go (W4.BaseIte _bt _ e1 e2 e3) = do
          s1 <- goE e1
          s2 <- goE e2
          s3 <- goE e3
          return $ S.L [ident "ite", s1, s2, s3]
        go (W4.BaseEq _bt e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "=", s1, s2]
        go (W4.NotPred e) = do
          s <- goE e
          return $ S.L [ident "notp", s]
        go (W4.ConjPred bm) = convertBoolMap "andp" True bm
        go (W4.BVSlt e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "bvslt", s1, s2]
        go (W4.BVUlt e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "bvult", s1, s2]
        go (W4.BVConcat _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "concat", s1, s2]
        go (W4.BVSelect idx n bv) = extract i j bv
          -- See SemMC.Formula.Parser.readExtract for the explanation behind
          -- these values.
          where i = intValue n + j - 1
                j = intValue idx

        -- Note that because the SemiRing has an identity element that
        -- always gets applied, resulting in lots of additional,
        -- unnecessary elements like: "(bvand #xffffffff TERM)".
        -- These will get manifested in the stored form (but generally
        -- _not_ via DSL-generated versions since they don't output
        -- via Printer) and result in longer stored forms.  They could
        -- be eliminated by checking for the identity (e.g. "if mul ==
        -- SR.one (WSum.sumRepr sm)") but the re-loaded representation
        -- will still use the SemiRing, so it's probably not worth the
        -- effort to reduce these.
        go (W4.SemiRingSum sm) =
          case WSum.sumRepr sm of
            W4.SemiRingBVRepr W4.BVArithRepr w ->
              let smul mul e = do
                    s <- goE e
                    return $ S.L [ ident "bvmul", bitvec (natValue w) (BV.asUnsigned mul), s]
                  sval v = return $ bitvec (natValue w) (BV.asUnsigned v)
                  add x y = return $ S.L [ ident "bvadd", x, y ]
              in WSum.evalM add smul sval sm
            W4.SemiRingBVRepr W4.BVBitsRepr w ->
              let smul mul e = do
                    s <- goE e
                    return $ S.L [ ident "bvand", bitvec (natValue w) (BV.asUnsigned mul), s]
                  sval v = return $ bitvec (natValue w) (BV.asUnsigned v)
                  add x y = let op = ident "bvxor" in return $ S.L [ op, x, y ]
              in WSum.evalM add smul sval sm
            W4.SemiRingIntegerRepr ->
              let smul mul e = do
                    s <- goE e
                    return $ S.L [ ident "intmul", int mul, s]
                  sval v = return $ int v
                  add x y = return $ S.L [ ident "intadd", x, y ]
              in WSum.evalM add smul sval sm
            W4.SemiRingRealRepr    -> error "SemiRingSum RealRepr not supported"

        go (W4.SemiRingProd pd) =
          case WSum.prodRepr pd of
            W4.SemiRingBVRepr W4.BVArithRepr w -> do
              let pmul x y = return $ S.L [ ident "bvmul", x, y ]
              maybeS <- WSum.prodEvalM pmul goE pd
              case maybeS of
                Just s -> return s
                Nothing -> return $ bitvec (natValue w) 1
            W4.SemiRingBVRepr W4.BVBitsRepr w -> do
              let pmul x y = return $ S.L [ ident "bvand", x, y ]
              maybeS <- WSum.prodEvalM pmul goE pd
              case maybeS of
                Just s -> return s
                Nothing -> return $ bitvec (natValue w) 1
            W4.SemiRingIntegerRepr -> do
              let pmul x y = return $ S.L [ ident "intmul", x, y ]
              maybeS <- WSum.prodEvalM pmul goE pd
              case maybeS of
                Just s -> return s
                Nothing -> return $ int 1
            W4.SemiRingRealRepr    -> error "convertApp W4.SemiRingProd Real unsupported"

        go (W4.SemiRingLe sr e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          case sr of
            W4.OrderedSemiRingIntegerRepr -> do
              return $ S.L [ ident "intle", s1, s2]
            W4.OrderedSemiRingRealRepr -> error $ "Printer: SemiRingLe is not supported for reals"

        go (W4.BVOrBits width bs) = do
          let op = ident "bvor"
          case W4.bvOrToList bs of
            [] -> return $ bitvec (NR.natValue width) 0
            (x:xs) -> do
              e <- goE x
              let f = (\acc b -> do
                          b' <- goE b
                          return $ S.L [op, b', acc])
              M.foldM f e xs
        go (W4.BVUdiv _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "bvudiv", s1, s2]
        go (W4.BVUrem _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "bvurem", s1, s2]
        go (W4.BVSdiv _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "bvsdiv", s1, s2]
        go (W4.BVSrem _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "bvsrem", s1, s2]
        go (W4.BVShl _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "bvshl", s1, s2]
        go (W4.BVLshr _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "bvlshr", s1, s2]
        go (W4.BVAshr _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "bvashr", s1, s2]
        go (W4.BVZext r e) = extend "zero" (intValue r) e
        go (W4.BVSext r e) = extend "sign" (intValue r) e
        go (W4.BVFill r e) = do
          s <- goE e
          return $ S.L [ S.L [ident "_", ident "bvfill", int (intValue r)]
                       , s
                       ]

        go (W4.BVToInteger e) = do
          s <- goE e
          return $ S.L [ident "bvToInteger", s]

        go (W4.SBVToInteger e) = do
          s <- goE e
          return $ S.L [ident "sbvToInteger", s]

        go (W4.FloatNeg _repr e) = do
          s <- goE e
          return $ S.L [ident "floatneg", s]
        go (W4.FloatAbs _repr e) = do
          s <- goE e
          return $ S.L [ident "floatabs", s]

        go (W4.IntDiv e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "intdiv", s1, s2]
        go (W4.IntMod e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "intmod", s1, s2]
        go (W4.IntAbs e1) = do
          s1 <- goE e1
          return $ S.L [ident "intabs", s1]
        go (W4.IntegerToBV e wRepr)  = do
          s <- goE e
          return $ S.L [ident "integerToBV"
                        , nat $ natValue wRepr
                        , s]

        go (W4.StructCtor _tps es) = do
          ss <- convertExprAssignment es
          return $ S.L [ident "struct", S.L ss]
        go (W4.StructField e ix _fieldTp) = do
          s <- goE e
          return $ S.L [ident "field"
                        , s
                        , int $ toInteger $ Ctx.indexVal ix
                        ]

        go (W4.UpdateArray _ _ e1 es e2) = do
          s1 <- goE e1
          ss <- convertExprAssignment es
          s2 <- goE e2
          case ss of
            [idx] -> return $ S.L [ ident "updateArray", s1, idx, s2]
            _ -> error $ "multidimensional arrays not supported"
        go (W4.SelectArray _ e es) = do
          s <- goE e
          ss <- convertExprAssignment es
          case ss of
            [idx] -> return $ S.L [ ident "select", s, idx]
            _ -> error $ "multidimensional arrays not supported"

        go (W4.ArrayMap _idxReprs _resRepr updateMap arr) = do
          updates <- mapM convertArrayUpdate (WAU.toList updateMap)
          arr' <- goE arr
          return $ S.L [ ident "arrayMap"
                       , S.L updates
                       , arr'
                       ]

        go app = error $ "unhandled App: " ++ show app

        convertArrayUpdate :: forall tp1 ctx . (Ctx.Assignment WIL.IndexLit ctx, W4.Expr t tp1) -> Memo t SExpr
        convertArrayUpdate (idxLits, e) = do
          e' <- goE e
          return $ S.L [ S.L (FC.toListFC convertIndexLit idxLits)
                       , e'
                       ]

        -- -- -- -- Helper functions! -- -- -- --

        goE :: forall tp' . W4.Expr t tp' -> Memo t SExpr
        goE = convertExpr

        extend :: forall w. Text -> Integer -> W4.Expr t (BaseBVType w) -> Memo t SExpr
        extend op r e = do
          let w = case W4.exprType e of BaseBVRepr len -> intValue len
              extension = r - w
          s <- goE e
          return $ S.L [ S.L [ ident "_", ident $ op <> "_extend", int extension ]
                        , s
                        ]

        extract :: forall tp'. Integer -> Integer -> W4.Expr t tp' -> Memo t SExpr
        extract i j bv = do
          s <- goE bv
          return $ S.L [ S.L [ ident "_", ident "extract", int i, int j ]
                        , s
                        ]

        convertBoolMap :: Text -> Bool -> BooM.BoolMap (W4.Expr t) -> Memo t SExpr
        convertBoolMap op base bm =
          let strBase b = if b
                          then S.L [ident "=", bitvec 1 0, bitvec 1 0]  -- true
                          else S.L [ident "=", bitvec 1 0, bitvec 1 1]  -- false
              strNotBase = strBase . not
          in case BooM.viewBoolMap bm of
               BooM.BoolMapUnit -> return $ strBase base
               BooM.BoolMapDualUnit -> return $ strNotBase base
               BooM.BoolMapTerms ts ->
                 let onEach e r = do
                       s <- arg e
                       return $ S.L [ident op, s, r]
                     arg (t, BooM.Positive) = goE t
                     arg (t, BooM.Negative) = do
                       s <- goE t
                       return $ S.L [ident "notp", s]
                 in F.foldrM onEach (strBase base) ts

convertIndexLit :: WIL.IndexLit tp -> SExpr
convertIndexLit il =
  case il of
    WIL.IntIndexLit iidx -> int iidx
    WIL.BVIndexLit irep bvidx -> bitvec (natValue irep) (BV.asUnsigned bvidx)

convertExprAssignment ::
  Ctx.Assignment (W4.Expr t) sh
  -> Memo t [SExpr]
convertExprAssignment es =
  mapM (\(Some e) -> convertExpr e) (FC.toListFC Some es)

convertFnApp ::
  W4.ExprSymFn t args ret
  -> Ctx.Assignment (W4.Expr t) args
  -> Memo t SExpr
convertFnApp fn args = do
  argSExprs <- convertExprAssignment args
  fnEnv <- MS.gets envFreeSymFnEnv
  case OMap.lookup (SomeExprSymFn fn) fnEnv of
    Just fnName ->
      return $ S.L $ (ident "call"):(ident fnName):argSExprs
    Nothing -> do
      varName <- freshFnName fn
      MS.modify' $ (\e -> e {envFreeSymFnEnv =  fnEnv OMap.|> ((SomeExprSymFn fn), varName)})
      return $ S.L $ (ident "call"):(ident varName):argSExprs


convertBaseType :: BaseTypeRepr tp -> SExpr
convertBaseType tp = case tp of
  W4.BaseBoolRepr -> S.A $ AId "Bool"
  W4.BaseIntegerRepr -> S.A $ AId "Int"
  W4.BaseRealRepr -> S.A $ AId "Real"
  W4.BaseStringRepr si -> S.L [S.A $ AId "String", convertStringInfo si]
  W4.BaseComplexRepr -> S.A $ AId "Complex"
  W4.BaseBVRepr wRepr -> S.L [S.A (AId "BV"), S.A (AInt (NR.intValue wRepr)) ]
  W4.BaseStructRepr tps -> S.L [ S.A (AId "Struct"), S.L (convertBaseTypes tps) ]
  W4.BaseArrayRepr ixs repr -> S.L [S.A (AId "Array"), S.L $ convertBaseTypes ixs , convertBaseType repr]
  W4.BaseFloatRepr (W4.FloatingPointPrecisionRepr eRepr sRepr) ->
    S.L [ S.A (AId "Float"), S.A (AInt (NR.intValue eRepr)), S.A (AInt (NR.intValue sRepr)) ]
  W4.BaseVariantRepr _ -> error "TODO RGS"



convertStringInfo :: StringInfoRepr si -> SExpr
convertStringInfo W4.Char8Repr = ident "Char8"
convertStringInfo W4.Char16Repr = ident "Char16"
convertStringInfo W4.UnicodeRepr = ident "Unicode"

-- | Convert an Assignment of base types into a list of base
-- types SExpr, where the left-to-right syntactic ordering
-- of the types is maintained.
convertBaseTypes ::
  Ctx.Assignment BaseTypeRepr tps
  -> [SExpr]
convertBaseTypes asn = FC.toListFC convertBaseType asn

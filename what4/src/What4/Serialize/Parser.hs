{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiWayIf #-}

-- | A parser for an s-expression representation of what4 expressions
module What4.Serialize.Parser
  ( deserializeExpr
  , deserializeExprWithConfig
  , deserializeSymFn
  , deserializeSymFnWithConfig
  , deserializeBaseType
  , readBaseTypes
  , Atom(..)
  , S.WellFormedSExpr(..)
  , Config(..)
  , defaultConfig
  , SomeSymFn(..)
  , type SExpr
  , parseSExpr
  , printSExpr
  ) where

import qualified Control.Monad.Except as E
import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.Reader as R
import qualified Data.BitVector.Sized as BV
import qualified Data.Foldable as F
import qualified Data.HashMap.Lazy as HM
import           Data.Kind
import qualified Data.SCargot.Repr.WellFormed as S

import           Data.Text ( Text )
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import           Text.Printf ( printf )

import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Parameterized.Ctx as Ctx
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as FC
import           What4.BaseTypes

import qualified What4.Expr.ArrayUpdateMap as WAU
import qualified What4.Expr.Builder as W4
import qualified What4.IndexLit as WIL
import qualified What4.Interface as W4

import           What4.Serialize.SETokens ( Atom(..), printSExpr, parseSExpr )
import qualified What4.Utils.Serialize as U
import           What4.Serialize.Printer ( SExpr )

import           Prelude

data SomeSymFn t = forall dom ret. SomeSymFn (W4.SymFn t dom ret)

data Config sym =
  Config
  { cSymFnLookup :: Text -> IO (Maybe (SomeSymFn sym))
  -- ^ The mapping of names to defined What4 SymFns.
  , cExprLookup :: Text -> IO (Maybe (Some (W4.SymExpr sym)))
  -- ^ The mapping of names to defined What4 expressions.
  }

defaultConfig :: (W4.IsSymExprBuilder sym, ShowF (W4.SymExpr sym)) => sym -> Config sym
defaultConfig _sym = Config { cSymFnLookup = const (return Nothing)
                            , cExprLookup = const (return Nothing)
                            }


-- | The lexical environment for parsing s-expressions and
-- procesing them into What4 terms.
data ProcessorEnv sym =
  ProcessorEnv
  { procSym :: sym
  -- ^ The symbolic What4 backend being used.
  , procSymFnLookup :: Text -> IO (Maybe (SomeSymFn sym))
    -- ^ The user-specified mapping of names to defined What4 SymFns.
  , procExprLookup :: Text -> IO (Maybe (Some (W4.SymExpr sym)))
  -- ^ The user-specified mapping of names to defined What4 expressions.
  , procLetEnv :: HM.HashMap Text (Some (W4.SymExpr sym))
  -- ^ The current lexical environment w.r.t. let-bindings
  -- encountered while parsing. N.B., these bindings are
  -- checked _before_ the \"global\" bindings implied by the
  -- user-specified lookup functions.
  , procLetFnEnv :: HM.HashMap Text (SomeSymFn sym)
  -- ^ The current lexical symfn environment
  -- w.r.t. letfn-bindings encountered while parsing. N.B.,
  -- these bindings are checked /before/ the \"global\"
  -- bindings implied by the user-specified lookup
  -- functions.
  }

type Processor sym a = E.ExceptT String (R.ReaderT (ProcessorEnv sym) IO) a

runProcessor :: ProcessorEnv sym -> Processor sym a -> IO (Either String a)
runProcessor env action = R.runReaderT (E.runExceptT action) env

lookupExpr :: Text -> Processor sym (Maybe (Some (W4.SymExpr sym)))
lookupExpr nm = do
  userLookupFn <- R.asks procExprLookup
  letEnv <- R.asks procLetEnv
  case HM.lookup nm letEnv of
    Nothing -> liftIO $ userLookupFn nm
    res -> return res

lookupFn :: Text -> Processor sym (Maybe (SomeSymFn sym))
lookupFn nm = do
  userLookupFn <- R.asks procSymFnLookup
  letEnv <- R.asks procLetFnEnv
  case HM.lookup nm letEnv of
    Nothing -> liftIO $ userLookupFn nm
    res -> return res


-- | @(deserializeExpr sym)@ is equivalent
-- to @(deserializeExpr' (defaultConfig sym))@.
deserializeExpr ::
  forall sym t st fs . (sym ~ W4.ExprBuilder t st fs)
  => sym
  -> SExpr
  -> IO (Either String (Some (W4.SymExpr sym)))
deserializeExpr sym = deserializeExprWithConfig sym cfg
  where cfg = defaultConfig sym

deserializeExprWithConfig ::
  forall sym t st fs . (sym ~ W4.ExprBuilder t st fs)
  => sym
  -> Config sym
  -> SExpr
  -> IO (Either String (Some (W4.SymExpr sym)))
deserializeExprWithConfig sym cfg sexpr = runProcessor env (readExpr sexpr)
  where env = ProcessorEnv { procSym = sym
                           , procSymFnLookup = cSymFnLookup cfg
                           , procExprLookup = cExprLookup cfg
                           , procLetEnv = HM.empty
                           , procLetFnEnv = HM.empty
                           }

-- | @(deserializeSymFn sym)@ is equivalent
-- to @(deserializeSymFn' (defaultConfig sym))@.
deserializeSymFn ::
  forall sym t st fs . (sym ~ W4.ExprBuilder t st fs)
  => sym
  -> SExpr
  -> IO (Either String (SomeSymFn sym))
deserializeSymFn sym = deserializeSymFnWithConfig sym cfg
  where cfg = defaultConfig sym

deserializeSymFnWithConfig ::
  forall sym t st fs . (sym ~ W4.ExprBuilder t st fs)
  => sym
  -> Config sym
  -> SExpr
  -> IO (Either String (SomeSymFn sym))
deserializeSymFnWithConfig sym cfg sexpr = runProcessor env (readSymFn sexpr)
  where env = ProcessorEnv { procSym = sym
                           , procSymFnLookup = cSymFnLookup cfg
                           , procExprLookup = cExprLookup cfg
                           , procLetEnv = HM.empty
                           , procLetFnEnv = HM.empty
                           }


deserializeBaseType ::
  SExpr
  -> Either String (Some BaseTypeRepr)
deserializeBaseType sexpr = readBaseType sexpr





-- * First pass of parsing turns the raw text into s-expressions.
--   This pass is handled by the code in What4.Serialize.SETokens

-- * Second pass of parsing: turning the s-expressions into symbolic expressions
-- and the overall templated formula

-- ** Utility functions

-- | Utility function for contextualizing errors. Prepends the given prefix
-- whenever an error is thrown.
prefixError :: (Monoid e, E.MonadError e m) => e -> m a -> m a
prefixError prefix act = E.catchError act (E.throwError . mappend prefix)

-- | Utility function for lifting a 'Maybe' into a 'MonadError'
fromMaybeError :: (E.MonadError e m) => e -> Maybe a -> m a
fromMaybeError err = maybe (E.throwError err) return


readBaseType ::
  forall m . (E.MonadError String m)
  => SExpr
  -> m (Some BaseTypeRepr)
readBaseType sexpr =
  case sexpr of
    S.WFSAtom (AId atom) ->
      case (T.unpack atom) of
        "Bool" -> return $ Some BaseBoolRepr
        "Int" -> return $ Some BaseIntegerRepr
        "Real" -> return $ Some BaseRealRepr
        "String" -> return $ Some (BaseStringRepr UnicodeRepr)
        "Complex" -> return $ Some BaseComplexRepr
        _ -> panic
    S.WFSList [(S.WFSAtom (AId "BV")), (S.WFSAtom (AInt w))]
      | Just (Some wRepr) <- someNat w
      , Just LeqProof <- testLeq (knownNat @1) wRepr
        -> return $ Some (BaseBVRepr wRepr)
      | otherwise
        -> panic
    S.WFSList [(S.WFSAtom (AId "Float")), (S.WFSAtom (AInt e)), (S.WFSAtom (AInt s))]
      | Just (Some eRepr) <- someNat e
      , Just (Some sRepr) <- someNat s
      , Just LeqProof <- testLeq (knownNat @2) eRepr
      , Just LeqProof <- testLeq (knownNat @2) sRepr
        -> return (Some (BaseFloatRepr (FloatingPointPrecisionRepr eRepr sRepr)))
      | otherwise -> panic
    S.WFSList [(S.WFSAtom (AId "Struct")), args] -> do
      Some tps <- readBaseTypes args
      return $ Some (BaseStructRepr tps)
    S.WFSList [S.WFSAtom (AId "Array"), ixArgs, tpArg] -> do
      Some ixs <- readBaseTypes ixArgs
      Some tp <- readBaseType tpArg
      case Ctx.viewAssign ixs of
        Ctx.AssignEmpty -> E.throwError $ "array type has no indices: " ++ show sexpr
        Ctx.AssignExtend _ _ -> return $ Some (BaseArrayRepr ixs tp)
    _ -> panic
  where
    panic = E.throwError $ "unknown base type: " ++ show sexpr

readBaseTypes ::
  forall m . (E.MonadError String m)
  => SExpr
  -> m (Some (Ctx.Assignment BaseTypeRepr))
readBaseTypes sexpr@(S.WFSAtom _) = E.throwError $ "expected list of base types: " ++ show sexpr
readBaseTypes (S.WFSList sexprs) = Ctx.fromList <$> mapM readBaseType sexprs

-- ** Parsing definitions

-- | Stores a NatRepr along with proof that its type parameter is a bitvector of
-- that length. Used for easy pattern matching on the LHS of a binding in a
-- do-expression to extract the proof.
data BVProof tp where
  BVProof :: forall n. (1 <= n) => NatRepr n -> BVProof (BaseBVType n)

-- | Given an expression, monadically either returns proof that it is a
-- bitvector or throws an error.
getBVProof :: (W4.IsExpr ex, E.MonadError String m) => ex tp -> m (BVProof tp)
getBVProof expr =
  case W4.exprType expr of
    BaseBVRepr n -> return $ BVProof n
    t -> E.throwError $ printf "expected BV, found %s" (show t)


-- | Operator type descriptions for parsing s-expression of
-- the form @(operator operands ...)@.
data Op sym where
    FloatOp1 :: (forall fpp . sym ->
                 W4.SymFloat sym fpp ->
                 IO (W4.SymFloat sym fpp))
             -> Op sym
    -- | Generic unary operator description.
    Op1 :: Ctx.Assignment BaseTypeRepr (Ctx.EmptyCtx Ctx.::> arg1)
        -> (sym ->
            W4.SymExpr sym arg1 ->
            IO (W4.SymExpr sym ret))
        -> Op sym
    -- | Generic dyadic operator description.
    Op2 :: Ctx.Assignment BaseTypeRepr (Ctx.EmptyCtx Ctx.::> arg1 Ctx.::> arg2)
        -> (sym ->
            W4.SymExpr sym arg1 ->
            W4.SymExpr sym arg2 ->
            IO (W4.SymExpr sym ret))
        -> Op sym
    -- | Generic triadic operator description.
    Op3 :: Ctx.Assignment BaseTypeRepr (Ctx.EmptyCtx Ctx.::> arg1 Ctx.::> arg2 Ctx.::> arg3)
        -> (sym ->
            W4.SymExpr sym arg1 ->
            W4.SymExpr sym arg2 ->
            W4.SymExpr sym arg3 ->
            IO (W4.SymExpr sym ret)
           )
        -> Op sym
    -- | Generic tetradic operator description.
    Op4 :: Ctx.Assignment
           BaseTypeRepr
           (Ctx.EmptyCtx Ctx.::> arg1 Ctx.::> arg2 Ctx.::> arg3 Ctx.::> arg4)
        -> ( sym ->
             W4.SymExpr sym arg1 ->
             W4.SymExpr sym arg2 ->
             W4.SymExpr sym arg3 ->
             W4.SymExpr sym arg4 ->
             IO (W4.SymExpr sym ret)
           )
        -> Op sym
    -- | Encapsulating type for a unary operation that takes one bitvector and
    -- returns another (in IO).
    BVOp1 :: (forall w . (1 <= w) =>
               sym ->
               W4.SymBV sym w ->
               IO (W4.SymBV sym w))
          -> Op sym
    -- | Binop with a bitvector return type, e.g., addition or bitwise operations.
    BVOp2 :: (forall w . (1 <= w) =>
               sym ->
               W4.SymBV sym w ->
               W4.SymBV sym w ->
               IO (W4.SymBV sym w))
          -> Op sym
    -- | Bitvector binop with a boolean return type, i.e., comparison operators.
    BVComp2 :: (forall w . (1 <= w) =>
                    sym ->
                    W4.SymBV sym w ->
                    W4.SymBV sym w ->
                    IO (W4.Pred sym))
                -> Op sym

-- | Lookup mapping operators to their Op definitions (if they exist)
lookupOp :: forall sym . W4.IsSymExprBuilder sym => Text -> Maybe (Op sym)
lookupOp name = HM.lookup name opTable


opTable :: (W4.IsSymExprBuilder sym) => HM.HashMap Text (Op sym)
opTable =
  HM.fromList [
  -- -- -- Boolean ops -- -- --
    ("andp", Op2 knownRepr $ W4.andPred)
  , ("orp", Op2 knownRepr $ W4.orPred)
  , ("xorp", Op2 knownRepr $ W4.xorPred)
  , ("notp", Op1 knownRepr $ W4.notPred)
  -- -- -- Float ops -- -- --
  , ("floatneg", FloatOp1 W4.floatNeg)
  , ("floatabs", FloatOp1 W4.floatAbs)
  -- -- -- Integer ops -- -- --
  , ("intmul", Op2 knownRepr $ W4.intMul)
  , ("intadd", Op2 knownRepr $ W4.intAdd)
  , ("intmod", Op2 knownRepr $ W4.intMod)
  , ("intdiv", Op2 knownRepr $ W4.intDiv)
  , ("intle", Op2 knownRepr $ W4.intLe)
  , ("intabs", Op1 knownRepr $ W4.intAbs)
  -- -- -- Bitvector ops -- -- --
  , ("bvand", BVOp2 W4.bvAndBits)
  , ("bvor", BVOp2 W4.bvOrBits)
  , ("bvadd", BVOp2 W4.bvAdd)
  , ("bvmul", BVOp2 W4.bvMul)
  , ("bvudiv", BVOp2 W4.bvUdiv)
  , ("bvurem", BVOp2 W4.bvUrem)
  , ("bvshl", BVOp2 W4.bvShl)
  , ("bvlshr", BVOp2 W4.bvLshr)
  , ("bvnand", BVOp2 $ \sym arg1 arg2 -> W4.bvNotBits sym =<< W4.bvAndBits sym arg1 arg2)
  , ("bvnor", BVOp2 $ \sym arg1 arg2 -> W4.bvNotBits sym =<< W4.bvOrBits sym arg1 arg2)
  , ("bvxor", BVOp2 W4.bvXorBits)
  , ("bvxnor", BVOp2 $ \sym arg1 arg2 -> W4.bvNotBits sym =<< W4.bvXorBits sym arg1 arg2)
  , ("bvsub", BVOp2 W4.bvSub)
  , ("bvsdiv", BVOp2 W4.bvSdiv)
  , ("bvsrem", BVOp2 W4.bvSrem)
  , ("bvsmod", error "bvsmod is not implemented")
  , ("bvashr", BVOp2 W4.bvAshr)
  , ("bvult", BVComp2 W4.bvUlt)
  , ("bvule", BVComp2 W4.bvUle)
  , ("bvugt", BVComp2 W4.bvUgt)
  , ("bvuge", BVComp2 W4.bvUge)
  , ("bvslt", BVComp2 W4.bvSlt)
  , ("bvsle", BVComp2 W4.bvSle)
  , ("bvsgt", BVComp2 W4.bvSgt)
  , ("bvsge", BVComp2 W4.bvSge)
  , ("bveq", BVComp2 W4.bvEq)
  , ("bvne", BVComp2 W4.bvNe)
  , ("bvneg", BVOp1 W4.bvNeg)
  , ("bvnot", BVOp1 W4.bvNotBits)
  -- -- -- Floating point ops -- -- --
  , ("fnegd", Op1 knownRepr $ W4.floatNeg @_ @Prec64)
  , ("fnegs", Op1 knownRepr $ W4.floatNeg @_ @Prec32)
  , ("fabsd", Op1 knownRepr $ W4.floatAbs @_ @Prec64)
  , ("fabss", Op1 knownRepr $ W4.floatAbs @_ @Prec32)
  , ("fsqrt", Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.floatSqrt @_ @Prec64 sym rm x)
  , ("fsqrts", Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.floatSqrt @_ @Prec32 sym rm x)
  , ("fnand", Op1 knownRepr $ W4.floatIsNaN @_ @Prec64)
  , ("fnans", Op1 knownRepr $ W4.floatIsNaN @_ @Prec32)
  , ("frsp", Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.floatCast @_ @Prec32 @Prec64 sym knownRepr rm x)
  , ("fp_single_to_double", Op1 knownRepr $ \sym ->
    W4.floatCast @_ @Prec64 @Prec32 sym knownRepr W4.RNE)
  , ("fp_binary_to_double",
     Op1 knownRepr $ \sym -> W4.floatFromBinary @_ @11 @53 sym knownRepr)
  , ("fp_binary_to_single",
     Op1 knownRepr $ \sym -> W4.floatFromBinary @_ @8 @24 sym knownRepr)
  , ("fp_double_to_binary", Op1 knownRepr $ W4.floatToBinary @_ @11 @53)
  , ("fp_single_to_binary", Op1 knownRepr $ W4.floatToBinary @_ @8 @24)
  , ("fctid", Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.floatToSBV @_ @64 @Prec64 sym knownRepr rm x)
  , ("fctidu", Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.floatToBV @_ @64 @Prec64 sym knownRepr rm x)
  , ("fctiw", Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.floatToSBV @_ @32 @Prec64 sym knownRepr rm x)
  , ("fctiwu", Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.floatToBV @_ @32 @Prec64 sym knownRepr rm x)
  , ("fcfid", Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.sbvToFloat @_ @64 @Prec64 sym knownRepr rm x)
  , ("fcfids", Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.sbvToFloat @_ @64 @Prec32 sym knownRepr rm x)
  , ("fcfidu", Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.bvToFloat @_ @64 @Prec64 sym knownRepr rm x)
  , ("fcfidus", Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.bvToFloat @_ @64 @Prec32 sym knownRepr rm x)
  , ("frti", Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.floatRound @_ @Prec64 sym rm x)
  , ("frtis", Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.floatRound @_ @Prec32 sym rm x)
  , ("fadd", Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    W4.floatAdd @_ @Prec64 sym rm x y)
  , ("fadds", Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    W4.floatAdd @_ @Prec32 sym rm x y)
  , ("fsub", Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    W4.floatSub @_ @Prec64 sym rm x y)
  , ("fsubs", Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    W4.floatSub @_ @Prec32 sym rm x y)
  , ("fmul", Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    W4.floatMul @_ @Prec64 sym rm x y)
  , ("fmuls", Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    W4.floatMul @_ @Prec32 sym rm x y)
  , ("fdiv", Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    W4.floatDiv @_ @Prec64 sym rm x y)
  , ("fdivs", Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    W4.floatDiv @_ @Prec32 sym rm x y)
  , ("fltd", Op2 knownRepr $ W4.floatLt @_ @Prec64)
  , ("flts", Op2 knownRepr $ W4.floatLt @_ @Prec32)
  , ("feqd", Op2 knownRepr $ W4.floatFpEq @_ @Prec64)
  , ("feqs", Op2 knownRepr $ W4.floatFpEq @_ @Prec32)
  , ("fled", Op2 knownRepr $ W4.floatLe @_ @Prec64)
  , ("fles", Op2 knownRepr $ W4.floatLe @_ @Prec32)
  , ("ffma", Op4 knownRepr $ \sym r x y z -> U.withRounding sym r $ \rm ->
    W4.floatFMA @_ @Prec64 sym rm x y z)
  , ("ffmas", Op4 knownRepr $ \sym r x y z ->
    U.withRounding sym r $ \rm -> W4.floatFMA @_ @Prec32 sym rm x y z)
  ]

-- | Verify a list of arguments has a single argument and
-- return it, else raise an error.
readOneArg ::
  forall sym t st fs . (sym ~ W4.ExprBuilder t st fs)
  => [SExpr]
  -> Processor sym (Some (W4.SymExpr sym))
readOneArg operands = do
  args <- readExprs operands
  case args of
    [arg] -> return arg
    _ -> E.throwError $ printf "expecting 1 argument, got %d" (length args)

-- | Verify a list of arguments has two arguments and return
-- it, else raise an error.
readTwoArgs ::
  forall sym t st fs . (sym ~ W4.ExprBuilder t st fs)
  => [SExpr]
  -> Processor sym (Some (W4.SymExpr sym), Some (W4.SymExpr sym))
readTwoArgs operands = do
  args <- readExprs operands
  case args of
    [arg1, arg2] -> return (arg1, arg2)
    _ -> E.throwError $ printf "expecting 2 arguments, got %d" (length args)

-- | Verify a list of arguments has three arguments and
-- return it, else raise an error.
readThreeArgs ::
  forall sym t st fs . (sym ~ W4.ExprBuilder t st fs)
  => [SExpr]
  -> Processor sym (Some (W4.SymExpr sym), Some (W4.SymExpr sym), Some (W4.SymExpr sym))
readThreeArgs operands = do
  args <- readExprs operands
  case args of
    [arg1, arg2, arg3] -> return (arg1, arg2, arg3)
    _ -> E.throwError $ printf "expecting 3 arguments, got %d" (length args)



-- | Reads an "application" form, i.e. @(operator operands ...)@.
readApp ::
  forall sym t st fs . (sym ~ W4.ExprBuilder t st fs)
  => SExpr
  -> [SExpr]
  -> Processor sym (Some (W4.SymExpr sym))
readApp (S.WFSAtom (AId "call")) (S.WFSAtom (AId fnName):operands) = do
  sym <- R.asks procSym
  maybeFn <- lookupFn fnName
  case maybeFn of
    Just (SomeSymFn fn) -> do
      args <- mapM readExpr operands
      assn <- exprAssignment (W4.fnArgTypes fn) args
      liftIO (Some <$> W4.applySymFn sym fn assn)
    Nothing -> E.throwError $ "The function name `"
               ++(T.unpack fnName)
               ++"` is not bound to a SymFn in the current Config."
readApp opRaw@(S.WFSAtom (AId "call")) operands = E.throwError
  $ "Unrecognized use of `call`: " ++ (T.unpack (printSExpr mempty (S.L (opRaw:operands))))
readApp opRaw@(S.WFSAtom (AId operator)) operands = do
  sym <- R.reader procSym
  prefixError ("in reading expression:\n"
               ++(T.unpack $ printSExpr mempty $ S.WFSList (opRaw:operands))++"\n") $
  -- Parse an expression of the form @(fnname operands ...)@
    case lookupOp @sym operator of
      Just (FloatOp1 fn) -> do
        args <- readExprs operands
        case args of
          [Some a1]
            | BaseFloatRepr _ <- W4.exprType a1 -> liftIO (Some <$> fn sym a1)
          _ -> E.throwError "Unable to unpack FloatOp1 arg in Formula.Parser readApp"
      Just (Op1 arg_types fn) -> do
        args <- readExprs operands
        exprAssignment arg_types args >>= \case
          Ctx.Empty Ctx.:> arg1 ->
            liftIO (Some <$> fn sym arg1)
      Just (Op2 arg_types fn) -> do
        args <- readExprs operands
        exprAssignment arg_types args >>= \case
          Ctx.Empty Ctx.:> arg1 Ctx.:> arg2 ->
              liftIO (Some <$> fn sym arg1 arg2)
      Just (Op3 arg_types fn) -> do
        args <- readExprs operands
        exprAssignment arg_types args >>= \case
          Ctx.Empty Ctx.:> arg1 Ctx.:> arg2 Ctx.:> arg3 ->
              liftIO (Some <$> fn sym arg1 arg2 arg3)
      Just (Op4 arg_types fn) -> do
        args <- readExprs operands
        exprAssignment arg_types args >>= \case
          Ctx.Empty Ctx.:> arg1 Ctx.:> arg2 Ctx.:> arg3 Ctx.:> arg4 ->
              liftIO (Some <$> fn sym arg1 arg2 arg3 arg4)
      Just (BVOp1 op) -> do
        Some expr <- readOneArg operands
        BVProof _ <- getBVProof expr
        liftIO $ Some <$> op sym expr
      Just (BVOp2 op) -> do
        (Some arg1, Some arg2)  <- readTwoArgs operands
        BVProof m <- prefixError "in arg 1: " $ getBVProof arg1
        BVProof n <- prefixError "in arg 2: " $ getBVProof arg2
        case testEquality m n of
          Just Refl -> liftIO (Some <$> op sym arg1 arg2)
          Nothing -> E.throwError $ printf "arguments to %s must be the same length, \
                                         \but arg 1 has length %s \
                                         \and arg 2 has length %s"
                                         operator
                                         (show m)
                                         (show n)
      Just (BVComp2 op) -> do
        (Some arg1, Some arg2)  <- readTwoArgs operands
        BVProof m <- prefixError "in arg 1: " $ getBVProof arg1
        BVProof n <- prefixError "in arg 2: " $ getBVProof arg2
        case testEquality m n of
          Just Refl -> liftIO (Some <$> op sym arg1 arg2)
          Nothing -> E.throwError $ printf "arguments to %s must be the same length, \
                                         \but arg 1 has length %s \
                                         \and arg 2 has length %s"
                                         operator
                                         (show m)
                                         (show n)
      Nothing ->
        -- Operators/syntactic-forms with types too
        -- complicated to nicely fit in the Op type
        case operator of
          "concat" -> do
            (Some arg1, Some arg2)  <- readTwoArgs operands
            BVProof _ <- prefixError "in arg 1: " $ getBVProof arg1
            BVProof _ <- prefixError "in arg 2: " $ getBVProof arg2
            liftIO (Some <$> W4.bvConcat sym arg1 arg2)
          "=" -> do
            (Some arg1, Some arg2)  <- readTwoArgs operands
            case testEquality (W4.exprType arg1) (W4.exprType arg2) of
              Just Refl -> liftIO (Some <$> W4.isEq sym arg1 arg2)
              Nothing -> E.throwError $
                printf "arguments must have same types, \
                       \but arg 1 has type %s \
                       \and arg 2 has type %s"
                (show (W4.exprType arg1))
                (show (W4.exprType arg2))
          "ite" -> do
            (Some test, Some then_, Some else_)  <- readThreeArgs operands
            case W4.exprType test of
              BaseBoolRepr ->
                case testEquality (W4.exprType then_) (W4.exprType else_) of
                  Just Refl -> liftIO (Some <$> W4.baseTypeIte sym test then_ else_)
                  Nothing -> E.throwError $
                    printf "then and else branches must have same type, \
                           \but then has type %s \
                           \and else has type %s"
                    (show (W4.exprType then_))
                    (show (W4.exprType else_))
              tp -> E.throwError $ printf "test expression must be a boolean; got %s" (show tp)
          "select" -> do
            (Some arr, Some idx)  <- readTwoArgs operands
            ArraySingleDim _ <- expectArrayWithIndex (W4.exprType idx) (W4.exprType arr)
            let idx' = Ctx.empty Ctx.:> idx
            liftIO (Some <$> W4.arrayLookup sym arr idx')
          "store" -> do
            (Some arr, Some idx, Some expr)  <- readThreeArgs operands
            ArraySingleDim resRepr <- expectArrayWithIndex (W4.exprType idx) (W4.exprType arr)
            case testEquality resRepr (W4.exprType expr) of
              Just Refl ->
                let idx' = Ctx.empty Ctx.:> idx
                in liftIO (Some <$> W4.arrayUpdate sym arr idx' expr)
              Nothing -> E.throwError $ printf "Array result type %s does not match %s"
                         (show resRepr)
                         (show (W4.exprType expr))
          "updateArray" -> do
            (Some arr, Some idx, Some expr)  <- readThreeArgs operands
            ArraySingleDim resRepr <- expectArrayWithIndex (W4.exprType idx) (W4.exprType arr)
            case testEquality resRepr (W4.exprType expr) of
              Just Refl ->
                let idx' = Ctx.empty Ctx.:> idx
                in liftIO (Some <$> W4.arrayUpdate sym arr idx' expr)
              Nothing -> E.throwError $ printf "Array result type %s does not match %s"
                         (show resRepr)
                         (show (W4.exprType expr))

          "arrayMap" ->
            -- arrayMap(idxs, array)

            -- The list of indexes is a list of pairs where each pair is:
            --
            -- > (indexList, expr)


            -- Each list of indexes is a list of 'IndexLit' (since we have multi-dimensional indexing)
            case operands of
              [updateSExprList, arrSExpr] -> do
                Some arrExpr <- readExpr arrSExpr
                case W4.exprType arrExpr of
                  BaseArrayRepr idxReprs arrTyRepr -> do
                    updateMap <- expectArrayUpdateMap idxReprs arrTyRepr updateSExprList
                    liftIO (Some <$> W4.sbMakeExpr sym (W4.ArrayMap idxReprs arrTyRepr updateMap arrExpr))
                  repr -> E.throwError $ unwords ["expected an array type for the value in 'arrayMap', but got", show repr]
              _ -> E.throwError $ unwords ["expected a list of indices and an array expression, but got", show operands]

          "field" -> do
            case operands of
              [rawStruct, S.WFSAtom (AInt rawIdx)] -> do
                Some struct  <- readExpr rawStruct
                case W4.exprType struct of
                  (BaseStructRepr fldTpReprs) ->
                    case Ctx.intIndex (fromInteger rawIdx) (Ctx.size fldTpReprs) of
                      Just (Some i) -> liftIO (Some <$> W4.structField sym struct i)
                      Nothing -> E.throwError $
                        unwords ["invalid struct index, got", show fldTpReprs, "and", show rawIdx]
                  srepr -> E.throwError $ unwords ["expected a struct, got", show srepr]
              _ -> E.throwError $ unwords ["expected an arg and an Int, got", show operands]
          "struct" -> do
            case operands of
              [S.WFSList rawFldExprs] -> do
                Some flds <- readExprsAsAssignment rawFldExprs
                liftIO (Some <$> W4.mkStruct sym flds)
              _ -> E.throwError $ unwords ["struct expects a single operand, got", show operands]
          "sbvToInteger" -> do
            (Some arg) <- readOneArg operands
            BVProof _ <- getBVProof arg
            liftIO $ Some <$> W4.sbvToInteger sym arg
          "bvToInteger" -> do
            (Some arg) <- readOneArg operands
            BVProof _ <- getBVProof arg
            liftIO $ Some <$> W4.bvToInteger sym arg
          "integerToBV" -> do
            case operands of
              [S.WFSAtom (ANat width), rawValExpr] -> do
                Some x <- readExpr rawValExpr
                case (mkNatRepr width, W4.exprType x) of
                  (Some w, BaseIntegerRepr)
                    | Just LeqProof <- isPosNat w -> do
                    liftIO (Some <$> W4.integerToBV sym x w)
                  srepr -> E.throwError $ unwords ["expected a non-zero natural and an integer, got", show srepr]
              _ -> E.throwError $ unwords ["integerToBV expects two operands, the first of which is a nat, got", show operands]
          _ -> E.throwError $ printf "couldn't parse application of %s" (printSExpr mempty opRaw)
-- Parse an expression of the form @((_ extract i j) x)@.
readApp (S.WFSList [S.WFSAtom (AId "_"), S.WFSAtom (AId "extract"), S.WFSAtom (AInt iInt), S.WFSAtom (AInt jInt)])
  args = prefixError "in reading extract expression: " $ do
  sym <- R.reader procSym
  (Some arg) <- readOneArg args
  -- The SMT-LIB spec represents extracts differently than Crucible does. Per
  -- SMT: "extraction of bits i down to j from a bitvector of size m to yield a
  -- new bitvector of size n, where n = i - j + 1". Per Crucible:
  --
  -- > -- | Select a subsequence from a bitvector.
  -- > bvSelect :: (1 <= n, idx + n <= w)
  -- >          => sym
  -- >          -> NatRepr idx  -- ^ Starting index, from 0 as least significant bit
  -- >          -> NatRepr n    -- ^ Number of bits to take
  -- >          -> SymBV sym w  -- ^ Bitvector to select from
  -- >          -> IO (SymBV sym n)
  --
  -- The "starting index" seems to be from the bottom, so that (in slightly
  -- pseudocode)
  --
  -- > > bvSelect sym 0 8 (0x01020304:[32])
  -- > 0x4:[8]
  -- > > bvSelect sym 24 8 (0x01020304:[32])
  -- > 0x1:[8]
  --
  -- Thus, n = i - j + 1, and idx = j.
  let nInt = iInt - jInt + 1
      idxInt = jInt
  Some nNat <- prefixError "in calculating extract length: " $ intToNatM nInt
  Some idxNat <- prefixError "in extract lower bound: " $ intToNatM idxInt
  LeqProof <- fromMaybeError "extract length must be positive" $ isPosNat nNat
  BVProof lenNat <- getBVProof arg
  LeqProof <- fromMaybeError "invalid extract for given bitvector" $
    testLeq (addNat idxNat nNat) lenNat
  liftIO (Some <$> W4.bvSelect sym idxNat nNat arg)
-- Parse an expression of the form @((_ zero_extend i) x)@ or @((_ sign_extend i) x)@.
readApp (S.WFSList [S.WFSAtom (AId "_"), S.WFSAtom (AId extend), S.WFSAtom (AInt iInt)])
  args
  | extend == "zero_extend" ||
    extend == "sign_extend" = prefixError (printf "in reading %s expression: " extend) $ do
      sym <- R.reader procSym
      Some arg <- readOneArg args
      Some iNat <- intToNatM iInt
      iPositive <- fromMaybeError "must extend by a positive length" $ isPosNat iNat
      BVProof lenNat <- getBVProof arg
      let newLen = addNat lenNat iNat
      liftIO $ withLeqProof (leqAdd2 (leqRefl lenNat) iPositive) $
        let op = if extend == "zero_extend" then W4.bvZext else W4.bvSext
        in Some <$> op sym newLen arg
readApp (S.WFSList [S.WFSAtom (AId "_"), S.WFSAtom (AId "bvfill"), S.WFSAtom (AInt width)]) args =
  prefixError "in reading bvfill expression" $ do
    sym <- R.reader procSym
    Some arg <- readOneArg args
    case W4.exprType arg of
      BaseBoolRepr -> do
        Some widthRep <- intToNatM width
        LeqProof <- fromMaybeError "must extend by a positive length" $ isPosNat widthRep
        liftIO (Some <$> W4.bvFill sym widthRep arg)
      tyrep -> E.throwError ("Invalid argument type to bvFill: " ++ show tyrep)
readApp rator rands = E.throwError $ ("readApp could not parse the following: "
                                      ++ (T.unpack (printSExpr mempty $ S.WFSList (rator:rands))))


-- | Try converting an 'Integer' to a 'NatRepr' or throw an error if not
-- possible.
intToNatM :: (E.MonadError String m) => Integer -> m (Some NatRepr)
intToNatM = fromMaybeError "integer must be non-negative to be a nat" . someNat

-- | Parse a list of array updates where each entry in the list is:
--
-- > (idxs, elt)
--
-- where each @idxs@ is a list (assignment) of indexes (with type @idxReprs@)
-- and each element is an expr.
--
-- NOTE: We assume that there are no duplicates in the list and apply the
-- updates in an arbitrary order.  This is true for any map serialized by this
-- library.
expectArrayUpdateMap
  :: forall sym t st fs tp i itp
   . (sym ~ W4.ExprBuilder t st fs)
  => Ctx.Assignment BaseTypeRepr (i Ctx.::> itp)
  -> BaseTypeRepr tp
  -> SExpr
  -> Processor sym (WAU.ArrayUpdateMap (W4.SymExpr sym) (i Ctx.::> itp) tp)
expectArrayUpdateMap idxReprs arrTyRepr updateSExprList =
  case updateSExprList of
    S.L items -> F.foldrM expectArrayUpdateEntry WAU.empty items
    _ -> E.throwError "Expected a list of array element updates in ArrayMap"
  where
    expectArrayUpdateEntry pair updateMap =
      case pair of
        S.L [S.L idxListExprs, elt] -> do
          idxs <- Ctx.traverseWithIndex (parseIndexLit idxListExprs) idxReprs
          Some x <- readExpr elt
          case testEquality arrTyRepr (W4.exprType x) of
            Just Refl -> return (WAU.insert arrTyRepr idxs x updateMap)
            Nothing -> E.throwError (concat [ "Invalid element type in ArrayMap update: expected "
                                            , show arrTyRepr
                                            , " but got "
                                            , show (W4.exprType x)])
        _ -> E.throwError "Unexpected ArrayMap update item structure"

-- | Safe list indexing
--
-- This version only traverses the list once (compared to computing the length
-- and then using unsafe indexing)
(!?) :: [a] -> Int -> Maybe a
lst !? idx
  | idx < 0 = Nothing
  | otherwise = go idx lst
  where
    go 0 (x:_xs) = Just x
    go i (_:xs) = go (i - 1) xs
    go _ [] = Nothing

-- | Parse a single 'WIL.IndexLit' out of a list of 'SExpr' (at the named index)
--
-- This is used to build the assignment of indexes
parseIndexLit :: [SExpr]
               -> Ctx.Index ctx tp
               -> BaseTypeRepr tp
               -> Processor sym (WIL.IndexLit tp)
parseIndexLit exprs idx repr
  | Just (S.A atom) <- exprs !? Ctx.indexVal idx =
      case (repr, atom) of
        (BaseBVRepr w, ABV w' val)
          | PN.intValue w == toInteger w' ->
            return (WIL.BVIndexLit w (BV.mkBV w val))
          | otherwise -> E.throwError ("Array update index bitvector size mismatch: expected " ++ show w ++ " but got " ++ show w')
        (BaseIntegerRepr, AInt i) -> return (WIL.IntIndexLit i)
        _ -> E.throwError ("Unexpected array update index type: " ++ show repr)
  | otherwise = E.throwError ("Invalid or missing array update index at " ++ show idx)

data ArrayJudgment :: BaseType -> BaseType -> Type where
  ArraySingleDim :: forall idx res.
                    BaseTypeRepr res
                 -> ArrayJudgment idx (BaseArrayType (Ctx.SingleCtx idx) res)

expectArrayWithIndex :: (E.MonadError String m) => BaseTypeRepr tp1 -> BaseTypeRepr tp2 -> m (ArrayJudgment tp1 tp2)
expectArrayWithIndex dimRepr (BaseArrayRepr idxTpReprs resRepr) =
  case Ctx.viewAssign idxTpReprs of
    Ctx.AssignExtend rest idxTpRepr ->
      case Ctx.viewAssign rest of
        Ctx.AssignEmpty ->
          case testEquality idxTpRepr dimRepr of
            Just Refl -> return $ ArraySingleDim resRepr
            Nothing -> E.throwError $ unwords ["Array index type", show idxTpRepr,
                                               "does not match", show dimRepr]
        _ -> E.throwError "multidimensional arrays are not supported"
expectArrayWithIndex _ repr = E.throwError $ unwords ["expected an array, got", show repr]

exprAssignment ::
  forall sym ctx ex . (W4.IsSymExprBuilder sym, ShowF (W4.SymExpr sym), ShowF ex, W4.IsExpr ex)
  => Ctx.Assignment BaseTypeRepr ctx
  -> [Some ex]
  -> Processor sym (Ctx.Assignment ex ctx)
exprAssignment tpAssns exs = do
  Some exsAsn <- return $ Ctx.fromList exs
  exsRepr <- return $ FC.fmapFC W4.exprType exsAsn
  case testEquality exsRepr tpAssns of
    Just Refl -> return exsAsn
    Nothing -> E.throwError $
      "Unexpected expression types for " ++ show exsAsn
      ++ "\nExpected: " ++ show tpAssns
      ++ "\nGot: " ++ show exsRepr


-- | Given the s-expressions for the bindings and body of a
-- let, parse the bindings into the Reader monad's state and
-- then parse the body with those newly bound variables.
readLetExpr ::
  forall sym t st fs . (sym ~ W4.ExprBuilder t st fs)
  => [SExpr]
  -- ^ Bindings in a let-expression.
  -> SExpr
  -- ^ Body of the let-expression.
  -> Processor sym (Some (W4.SymExpr sym))
readLetExpr [] body = readExpr body
readLetExpr ((S.WFSList [S.WFSAtom (AId x), e]):rst) body = do
  v <- readExpr e
  R.local (\c -> c {procLetEnv = (HM.insert x v) $ procLetEnv c}) $
    readLetExpr rst body
readLetExpr bindings _body = E.throwError $
  "invalid s-expression for let-bindings: " ++ (show bindings)


readLetFnExpr ::
  forall sym t st fs . (sym ~ W4.ExprBuilder t st fs)
  => [SExpr]
  -- ^ Bindings in a let-expression.
  -> SExpr
  -- ^ Body of the let-expression.
  -> Processor sym (Some (W4.SymExpr sym))
readLetFnExpr [] body = readExpr body
readLetFnExpr ((S.WFSList [S.WFSAtom (AId f), e]):rst) body = do
  v <- readSymFn e
  R.local (\c -> c {procLetFnEnv = (HM.insert f v) $ procLetFnEnv c}) $
    readLetExpr rst body
readLetFnExpr bindings _body = E.throwError $
  "invalid s-expression for let-bindings: " ++ (show bindings)

  
-- | Parse an arbitrary expression.
readExpr ::
  forall sym t st fs . (sym ~ W4.ExprBuilder t st fs)
  => SExpr
  -> Processor sym (Some (W4.SymExpr sym))
readExpr (S.WFSAtom (AInt n)) = do
  sym <- R.reader procSym
  liftIO $ (Some <$> W4.intLit sym n)
readExpr (S.WFSAtom (ANat _)) =
  E.throwError "Bare Natural literals are no longer used"
readExpr (S.WFSAtom (ABool b)) = do
  sym <- R.reader procSym
  liftIO $ return $ Some $ W4.backendPred sym b
readExpr (S.WFSAtom (AFloat (Some repr) bf)) = do
  sym <- R.reader procSym
  liftIO $ (Some <$> W4.floatLit sym repr bf)
readExpr (S.WFSAtom (AStr prefix content)) = do
  sym <- R.reader procSym
  case prefix of
    (Some W4.UnicodeRepr) -> do
      s <- liftIO $ W4.stringLit sym $ W4.UnicodeLiteral content
      return $ Some $ s
    (Some W4.Char8Repr) -> do
      s <- liftIO $ W4.stringLit sym $ W4.Char8Literal $ T.encodeUtf8 content
      return $ Some $ s
    (Some W4.Char16Repr) -> E.throwError $ "Char16 strings are not yet supported"
readExpr (S.WFSAtom (AReal _)) = E.throwError $ "TODO: support readExpr for real literals"
readExpr (S.WFSAtom (ABV len val)) = do
  -- This is a bitvector literal.
  sym <- R.reader procSym
  -- The following two patterns should never fail, given that during parsing we
  -- can only construct BVs with positive length.
  case someNat (toInteger len) of
    Just (Some lenRepr) -> do
        pf <- case isPosNat lenRepr of
                Just pf -> return pf
                Nothing -> E.throwError "What4.Serialize.Parser.readExpr isPosNat failure"
        liftIO $ withLeqProof pf (Some <$> W4.bvLit sym lenRepr (BV.mkBV lenRepr val))
    Nothing -> E.throwError "SemMC.Formula.Parser.readExpr someNat failure"
  -- Just (Some lenRepr) <- return $ someNat (toInteger len)
  -- let Just pf = isPosNat lenRepr
  -- liftIO $ withLeqProof pf (Some <$> W4.bvLit sym lenRepr val)
-- Let-bound variable
readExpr (S.WFSAtom (AId name)) = do
  maybeBinding <- lookupExpr name
  -- We first check the local lexical environment (i.e., the
  -- in-scope let-bindings) before consulting the "global"
  -- scope.
  case maybeBinding of
    -- simply return it's bound value
    Just binding -> return binding
    Nothing -> E.throwError $ ("Unbound variable encountered during deserialization: "
                               ++ (T.unpack name))
readExpr (S.WFSList ((S.WFSAtom (AId "let")):rhs)) =
  case rhs of
    [S.WFSList bindings, body] -> readLetExpr bindings body
    _ -> E.throwError "ill-formed let s-expression"
readExpr (S.WFSList ((S.WFSAtom (AId "letfn")):rhs)) =
  case rhs of
    [S.WFSList bindings, body] -> readLetFnExpr bindings body
    _ -> E.throwError "ill-formed letfn s-expression"
readExpr (S.WFSList []) = E.throwError "ill-formed empty s-expression"
readExpr (S.WFSList (operator:operands)) = readApp operator operands



-- | Parse multiple expressions in a list.
readExprs ::
  forall sym t st fs . (sym ~ W4.ExprBuilder t st fs)
  => [SExpr]
  -> Processor sym [Some (W4.SymExpr sym)]
readExprs exprs = mapM readExpr exprs

readExprsAsAssignment ::
  forall sym t st fs . (sym ~ W4.ExprBuilder t st fs)
  => [SExpr]
  -> Processor sym (Some (Ctx.Assignment (W4.SymExpr sym)))
readExprsAsAssignment exprs = Ctx.fromList <$> readExprs exprs


readFnType ::
  forall sym . (W4.IsSymExprBuilder sym, ShowF (W4.SymExpr sym))
  => SExpr
  -> Processor sym ([Some BaseTypeRepr], Some BaseTypeRepr)
readFnType (S.WFSList ((S.WFSAtom (AId "->")):typeSExprs)) =
  case unsnoc typeSExprs of
    Nothing ->
      E.throwError $ ("invalid type signature for function: "
                      ++ (T.unpack $ printSExpr mempty (S.L typeSExprs)))
    Just (domSExps, retSExp) -> do
      dom <- mapM readBaseType domSExps
      ret <- readBaseType retSExp
      return (dom, ret)
readFnType sexpr =
  E.throwError $ ("invalid type signature for function: "
                  ++ (T.unpack $ printSExpr mempty sexpr))

-- | If the list is empty, return 'Nothing'. If the list is non-empty, return
-- @'Just' (xs, x)@, where @xs@ is equivalent to calling 'init' on the list and
-- @x@ is equivalent to calling 'last' on the list.
unsnoc :: [a] -> Maybe ([a], a)
unsnoc []     = Nothing
unsnoc (x:xs) = case unsnoc xs of
                  Nothing    -> Just ([], x)
                  Just (a,b) -> Just (x:a, b)

readFnArgs ::
  forall sym . (W4.IsSymExprBuilder sym, ShowF (W4.SymExpr sym))
  => [SExpr]
  -> Processor sym [Text]
readFnArgs [] = return []
readFnArgs ((S.WFSAtom (AId name)):rest) = do
  names <- (readFnArgs rest)
  return $ name:names
readFnArgs (badArg:_) =
  E.throwError $ ("invalid function argument encountered: "
                  ++ (T.unpack $ printSExpr mempty badArg))

someVarExpr ::
    forall sym . (W4.IsSymExprBuilder sym, ShowF (W4.SymExpr sym))
  => sym
  -> Some (W4.BoundVar sym)
  -> Some (W4.SymExpr sym)
someVarExpr sym (Some bv) = Some (W4.varExpr sym bv)


readSymFn ::
  forall sym t st fs . (sym ~ W4.ExprBuilder t st fs)
  => SExpr
  -> Processor sym (SomeSymFn sym)
readSymFn (S.WFSList [ S.WFSAtom (AId "definedfn")
                     , S.WFSAtom (AStr _ rawSymFnName)
                     , rawFnType
                     , S.WFSList argVarsRaw
                     , bodyRaw
                     ]) = do
  sym <- R.reader procSym
  symFnName <- case W4.userSymbol (T.unpack rawSymFnName) of
                 Left _ -> E.throwError $ ("Bad symbolic function name : "
                                           ++ (T.unpack rawSymFnName))
                 Right solverSym -> return solverSym
  argNames <- readFnArgs argVarsRaw
  (argTys, _retTy) <- readFnType rawFnType
  E.when (not (length argTys == length argNames)) $
    E.throwError $ "Function type expected "
    ++ (show $ length argTys)
    ++ " args but found "
    ++ (show $ length argNames)
  argVars <- mapM (\(name, (Some ty)) ->
                     case W4.userSymbol (T.unpack name) of
                       Left _ -> E.throwError $ "Bad arg name : " ++ (T.unpack name)
                       Right solverSym -> liftIO $ Some <$> W4.freshBoundVar sym solverSym ty)
             $ zip argNames argTys
  (Some body) <- let newBindings = HM.fromList
                                   $ zip argNames
                                   $ map (someVarExpr sym) argVars
                 in R.local
                    (\env -> env {procLetEnv = HM.union (procLetEnv env) newBindings})
                    $ readExpr bodyRaw
  Some argVarAssignment <- return $ Ctx.fromList argVars
  symFn <- liftIO $ W4.definedFn sym symFnName argVarAssignment body W4.UnfoldConcrete
  return $ SomeSymFn symFn
readSymFn badSExp@(S.WFSList ((S.WFSAtom (AId "definedfn")):_)) =
  E.throwError $ ("invalid `definedfn`: " ++ (T.unpack $ printSExpr mempty badSExp))
readSymFn (S.WFSList [ S.WFSAtom (AId "uninterpfn")
                     , S.WFSAtom (AStr _ rawSymFnName)
                     , rawFnType
                     ]) = do
  sym <- R.reader procSym
  symFnName <- case W4.userSymbol (T.unpack rawSymFnName) of
                 Left _ -> E.throwError $ ("Bad symbolic function name : "
                                           ++ (T.unpack rawSymFnName))
                 Right solverSym -> return solverSym
  (argTys, (Some retTy)) <- readFnType rawFnType
  Some domain <- return $ Ctx.fromList argTys
  symFn <- liftIO $ W4.freshTotalUninterpFn sym symFnName domain retTy
  return $ SomeSymFn symFn
readSymFn badSExp@(S.WFSList ((S.WFSAtom (AId "uninterpfn")):_)) =
  E.throwError $ ("invalid `uninterpfn`: " ++ (T.unpack $ printSExpr mempty badSExp))
readSymFn sexpr = E.throwError ("invalid function definition: "
                                ++ (T.unpack $ printSExpr mempty sexpr))

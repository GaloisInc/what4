{-
Module           : What4.Protocol.VerilogWriter.Backend
Copyright        : (c) Galois, Inc 2020
Maintainer       : Jennifer Paykin <jpaykin@galois.com>
License          : BSD3

Convert What4 expressions into the data types defined in the @What4.Protocol.VerilogWriter.AST@ module.
-}
{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, ScopedTypeVariables, RankNTypes,
  TypeApplications, PolyKinds, DataKinds, ExplicitNamespaces, TypeOperators,
  LambdaCase, FlexibleContexts, LambdaCase, OverloadedStrings #-}

module What4.Protocol.VerilogWriter.Backend
  ( exprToVerilogExpr
  )
  where


import           Control.Monad (foldM)
import           Control.Monad.State (get)
import           Control.Monad.Except (MonadError(..))
import qualified Data.BitVector.Sized as BV
import           Data.List.NonEmpty ( NonEmpty(..) )

import           Data.Parameterized.Context
import           Data.Parameterized.Some (Some(..))
import           GHC.TypeNats


import qualified What4.Expr.BoolMap as BMap
import           What4.BaseTypes as WT
import           What4.Expr.Builder
import           What4.Interface
import qualified What4.SemiRing as SR
import           What4.Symbol
import qualified What4.Expr.WeightedSum as WS
import qualified What4.Expr.UnaryBV as UBV

import What4.Protocol.VerilogWriter.AST

doNotSupportError :: MonadError String m => String -> m a
doNotSupportError cstr = throwError $ doNotSupportMsg ++ cstr

doNotSupportMsg :: String
doNotSupportMsg = "the Verilog backend to What4 does not support "

-- | Convert a What4 expresssion into a Verilog expression and return a
-- name for that expression's result.
exprToVerilogExpr ::
  (IsExprBuilder sym, SymExpr sym ~ Expr n) =>
  Expr n tp ->
  VerilogM sym n (IExp tp)
exprToVerilogExpr e = do
  cache <- vsExpCache <$> get
  let cacheEval go = idxCacheEval cache e (go e)
  cacheEval $
    \case
      SemiRingLiteral (SR.SemiRingBVRepr _ w) i _ ->
        litBV w i
      SemiRingLiteral _ _ _ ->
        doNotSupportError "non-bit-vector literals"
      BoolExpr b _   -> litBool b
      StringExpr _ _ -> doNotSupportError "strings"
      FloatExpr{} -> doNotSupportError "floating-point values"
      AppExpr app -> appExprVerilogExpr app
      NonceAppExpr n -> nonceAppExprVerilogExpr n
      BoundVarExpr x ->
        do name <- addBoundInput x (bvarIdentifier x)
           return $ Ident (bvarType x) name

bvarIdentifier :: ExprBoundVar t tp -> Identifier
bvarIdentifier = solverSymbolAsText . bvarName

nonceAppExprVerilogExpr ::
  (IsExprBuilder sym, SymExpr sym ~ Expr n) =>
  NonceAppExpr n tp ->
  VerilogM sym n (IExp tp)
nonceAppExprVerilogExpr nae =
  case nonceExprApp nae of
    Forall _ _ -> doNotSupportError "universal quantification"
    Exists _ _ -> doNotSupportError "existential quantification"
    ArrayFromFn _ -> doNotSupportError "arrays"
    MapOverArrays _ _ _ -> doNotSupportError "arrays"
    ArrayTrueOnEntries _ _ -> doNotSupportError "arrays"
    FnApp f Empty -> do
      name <- addFreshInput (Some idx) (Some tp) base
      return $ Ident tp name
        where
          tp = symFnReturnType f
          idx = symFnId f
          base = solverSymbolAsText (symFnName f)
    -- TODO: inline defined functions?
    -- TODO: implement uninterpreted functions as uninterpreted functions
    FnApp _ _ -> doNotSupportError "named function applications"
    Annotation _ _ e -> exprToVerilogExpr e

boolMapToExpr ::
  (IsExprBuilder sym, SymExpr sym ~ Expr n) =>
  Bool ->
  Bool ->
  Binop WT.BaseBoolType WT.BaseBoolType ->
  BMap.BoolMap (Expr n) ->
  VerilogM sym n (IExp WT.BaseBoolType)
boolMapToExpr u du op es =
  let pol (x,Positive) = exprToVerilogExpr x
      pol (x,Negative) = unop Not =<< exprToVerilogExpr x
  in
  case BMap.viewBoolMap es of
    BMap.BoolMapUnit -> litBool u
    BMap.BoolMapDualUnit -> litBool du
    BMap.BoolMapTerms (t:|[]) -> pol t
    BMap.BoolMapTerms (t:|ts) -> do
      t' <- pol t
      ts' <- mapM pol ts
      foldM (binop op) t' ts'

leqSubPos :: (1 <= m, 1 <= n, n+1 <= m) => NatRepr m -> NatRepr n -> LeqProof 1 (m - n)
leqSubPos mr nr =
  case (plusComm nr one, plusMinusCancel one nr) of
    (Refl, Refl) ->
      leqSub2 (leqProof (nr `addNat` one) mr) (leqProof nr nr)
  where one = knownNat :: NatRepr 1

leqSuccLeft :: (n + 1 <= m) => p m -> NatRepr n -> LeqProof n m
leqSuccLeft mr nr =
  case (plusComm nr one, addPrefixIsLeq nr one) of
    (Refl, LeqProof) ->
      leqTrans (addIsLeq nr one) (leqProof (nr `addNat` one) mr)
  where one = knownNat :: NatRepr 1

appExprVerilogExpr ::
  (IsExprBuilder sym, SymExpr sym ~ Expr n) =>
  AppExpr n tp ->
  VerilogM sym n (IExp tp)
appExprVerilogExpr = appVerilogExpr . appExprApp

appVerilogExpr ::
  (IsExprBuilder sym, SymExpr sym ~ Expr n) =>
  App (Expr n) tp ->
  VerilogM sym n (IExp tp)
appVerilogExpr app =
  case app of
    -- Generic operations
    BaseIte _ _ b etrue efalse -> do
      b' <- exprToVerilogExpr b
      etrue' <- exprToVerilogExpr etrue
      efalse' <- exprToVerilogExpr efalse
      mux b' etrue' efalse'
    BaseEq _ e1 e2 -> do
      e1' <- exprToVerilogExpr e1
      e2' <- exprToVerilogExpr e2
      binop Eq e1' e2'

    -- Boolean operations
    NotPred e -> do
      e' <- exprToVerilogExpr e
      unop Not e'
    --DisjPred es -> boolMapToExpr False True Or es
    ConjPred es -> boolMapToExpr True False And (BMap.getConjMap es)

    -- Semiring operations
    -- We only support bitvector semiring operations
    SemiRingSum s
      | SR.SemiRingBVRepr SR.BVArithRepr w <- WS.sumRepr s -> do
        let scalMult' c e = scalMult w BVMul c =<< exprToVerilogExpr e
        WS.evalM (binop BVAdd) scalMult' (litBV w) s
      | SR.SemiRingBVRepr SR.BVBitsRepr w <- WS.sumRepr s ->
        let scalMult' c e = scalMult w BVAnd c =<< exprToVerilogExpr e in
        WS.evalM (binop BVXor) scalMult' (litBV w) s
    SemiRingSum _ -> doNotSupportError "semiring operations on non-bitvectors"
    SemiRingProd p
      | SR.SemiRingBVRepr SR.BVArithRepr w <- WS.prodRepr p ->
        WS.prodEvalM (binop BVMul) exprToVerilogExpr p >>= \case
          Nothing -> litBV w (BV.mkBV w 1)
          Just e  -> return e
      | SR.SemiRingBVRepr SR.BVBitsRepr w <- WS.prodRepr p ->
        WS.prodEvalM (binop BVAnd) exprToVerilogExpr p >>= \case
          Nothing -> litBV w (BV.maxUnsigned w)
          Just e  -> return e
    SemiRingProd _ -> doNotSupportError "semiring operations on non-bitvectors"
    -- SemiRingLe only accounts for Nats, Integers, and Reals, not bitvectors
    SemiRingLe _ _ _ -> doNotSupportError "semiring operations on non-bitvectors"

    -- Arithmetic operations
    RealIsInteger _ -> doNotSupportError "real numbers"

    IntDiv _ _ -> doNotSupportError "integers"
    IntMod _ _ -> doNotSupportError "integers"
    IntAbs _ -> doNotSupportError "integers"
    IntDivisible _ _ -> doNotSupportError "integers"

    RealDiv _ _ -> doNotSupportError "real numbers"
    RealSqrt _ -> doNotSupportError "real numbers"

    -- Irrational numbers
    RealSpecialFunction{} -> doNotSupportError "real numbers"
    RoundEvenReal _ -> doNotSupportError "real numbers"

    -- Bitvector operations
    BVTestBit i e -> do v <- exprToVerilogExpr e
                        bit v (fromIntegral i)
    BVSlt e1 e2 ->
      do e1' <- signed =<< exprToVerilogExpr e1
         e2' <- signed =<< exprToVerilogExpr e2
         binop Lt e1' e2'
    BVUlt e1 e2 ->
      do e1' <- exprToVerilogExpr e1
         e2' <- exprToVerilogExpr e2
         binop Lt e1' e2'

    BVOrBits w bs ->
      do exprs <- mapM exprToVerilogExpr (bvOrToList bs)
         case exprs of
           [] -> litBV w (BV.zero w)
           e:es -> foldM (binop BVOr) e es
    BVUnaryTerm ubv -> UBV.sym_evaluate (\i -> litBV w (BV.mkBV w i)) ite' ubv
      where
        w = UBV.width ubv
        ite' e e1 e0 = do e' <- exprToVerilogExpr e
                          mux e' e0 e1

    BVConcat size12 e1 e2 -> do e1' <- exprToVerilogExpr e1
                                e2' <- exprToVerilogExpr e2
                                concat2 size12 e1' e2'
    BVSelect start len bv -> do e <- exprToVerilogExpr bv
                                bitSelect e start len
    BVFill len b -> do e <- exprToVerilogExpr b
                       e1 <- litBV len (BV.maxUnsigned len)
                       e2 <- litBV len (BV.zero len)
                       mux e e1 e2
    BVUdiv _   bv1 bv2 ->
      do bv1' <- exprToVerilogExpr bv1
         bv2' <- exprToVerilogExpr bv2
         binop BVDiv bv1' bv2'
    BVUrem _   bv1 bv2 ->
      do bv1' <- exprToVerilogExpr bv1
         bv2' <- exprToVerilogExpr bv2
         binop BVRem bv1' bv2'
    BVSdiv _   bv1 bv2 ->
      do bv1' <- signed =<< exprToVerilogExpr bv1
         bv2' <- signed =<< exprToVerilogExpr bv2
         binop BVDiv bv1' bv2'
    BVSrem _   bv1 bv2 ->
      do bv1' <- signed =<< exprToVerilogExpr bv1
         bv2' <- signed =<< exprToVerilogExpr bv2
         binop BVRem bv1' bv2'
    BVShl  _   bv1 bv2 -> do e1 <- exprToVerilogExpr bv1
                             e2 <- exprToVerilogExpr bv2
                             binop BVShiftL e1 e2
    BVLshr _   bv1 bv2 -> do e1 <- exprToVerilogExpr bv1
                             e2 <- exprToVerilogExpr bv2
                             binop BVShiftR e1 e2
    BVAshr _   bv1 bv2 -> do e1 <- signed =<< exprToVerilogExpr bv1
                             e2 <- exprToVerilogExpr bv2
                             binop BVShiftRA e1 e2
    BVRol  w   bv1 bv2 ->
      do e1 <- exprToVerilogExpr bv1
         case bv2 of
           SemiRingLiteral (SR.SemiRingBVRepr _ _) n _ | n <= BV.mkBV w (intValue w) ->
             mkLet (BVRotateL w e1 n)
           _ -> doNotSupportError "non-constant bit rotations"
    BVRor  w   bv1 bv2 ->
      do e1 <- exprToVerilogExpr bv1
         case bv2 of
           SemiRingLiteral (SR.SemiRingBVRepr _ _) n _ | n <= BV.mkBV w (intValue w) ->
             mkLet (BVRotateR w e1 n)
           _ -> doNotSupportError "non-constant bit rotations"
    BVZext w e ->
      withLeqProof (leqSuccLeft w ew) $
      withLeqProof (leqSubPos w ew) $
      case minusPlusCancel w ew of
        Refl ->
          do e' <- exprToVerilogExpr e
             let n = w `subNat` ew
             zeros <- litBV n (BV.zero n)
             concat2 w zeros e'
      where ew = bvWidth e
    BVSext w e ->
      withLeqProof (leqSuccLeft w ew) $
      withLeqProof (leqSubPos w ew) $
      case minusPlusCancel w ew of
        Refl ->
          do e' <- exprToVerilogExpr e
             let n = w `subNat` ew
             zeros <- litBV n (BV.zero n)
             ones <- litBV n (BV.maxUnsigned n)
             sgn <- bit e' (fromIntegral (natValue w) - 1)
             ext <- mux sgn ones zeros
             concat2 w ext e'
      where ew = bvWidth e
    BVPopcount _ _ ->
      doNotSupportError "bit vector population count" -- TODO
    BVCountTrailingZeros _ _ ->
      doNotSupportError "bit vector count trailing zeros" -- TODO
    BVCountLeadingZeros  _ _ ->
      doNotSupportError "bit vector count leading zeros" -- TODO

    -- Float operations
    FloatNeg _ _ -> doNotSupportError "floats"
    FloatAbs _ _ -> doNotSupportError "floats"
    FloatSqrt _ _ _ -> doNotSupportError "floats"
    FloatAdd  _ _ _ _ -> doNotSupportError "floats"
    FloatSub  _ _ _ _ -> doNotSupportError "floats"
    FloatMul  _ _ _ _ -> doNotSupportError "floats"
    FloatDiv _ _ _ _ -> doNotSupportError "floats"
    FloatRem _ _ _ -> doNotSupportError "floats"
    FloatFMA _ _ _ _ _ -> doNotSupportError "floats"
    FloatFpEq _ _ -> doNotSupportError "floats"
    FloatLe _ _ -> doNotSupportError "floats"
    FloatLt _ _ -> doNotSupportError "floats"

    FloatIsNaN _ -> doNotSupportError "floats"
    FloatIsInf _ -> doNotSupportError "floats"
    FloatIsZero _ -> doNotSupportError "floats"
    FloatIsPos _ -> doNotSupportError "floats"
    FloatIsNeg _ -> doNotSupportError "floats"
    FloatIsSubnorm _ -> doNotSupportError "floats"
    FloatIsNorm _ -> doNotSupportError "floats"

    FloatCast _ _ _ -> doNotSupportError "floats"
    FloatRound _ _ _ -> doNotSupportError "floats"
    FloatFromBinary _ _ -> doNotSupportError "floats"
    FloatToBinary _ _ -> doNotSupportError "floats"
    BVToFloat _ _ _ -> doNotSupportError "floats"
    SBVToFloat _ _ _ -> doNotSupportError "floats"
    RealToFloat _ _ _ -> doNotSupportError "floats"
    FloatToBV _ _ _ -> doNotSupportError "floats"
    FloatToSBV _ _ _ -> doNotSupportError "floats"
    FloatToReal _ -> doNotSupportError "floats"
    FloatSpecialFunction _ _ _ -> doNotSupportError "floats"

    -- Array operations
    ArrayMap _ _ _ _ -> doNotSupportError "arrays"
    ConstantArray _ _ _ -> doNotSupportError "arrays"
    UpdateArray _ _ _ _ _ -> doNotSupportError "arrays"
    SelectArray _ _ _ -> doNotSupportError "arrays"
    CopyArray _ _ _ _ _ _ _ _ _ -> doNotSupportError "arrays"
    SetArray _ _ _ _ _ _ _ -> doNotSupportError "arrays"
    EqualArrayRange _ _ _ _ _ _ _ _ _ -> doNotSupportError "arrays"

    -- Conversions
    IntegerToReal _ -> doNotSupportError "integers"
    RealToInteger _ -> doNotSupportError "integers"
    BVToInteger _ -> doNotSupportError "integers"
    SBVToInteger _ -> doNotSupportError "integers"
    IntegerToBV _ _ -> doNotSupportError "integers"
    RoundReal _ -> doNotSupportError "real numbers"
    FloorReal _ -> doNotSupportError "real numbers"
    CeilReal _ -> doNotSupportError "real numbers"

    -- Complex operations
    Cplx _ -> doNotSupportError "complex numbers"
    RealPart _ -> doNotSupportError "complex numbers"
    ImagPart _ -> doNotSupportError "complex Numbers"

    -- Structs
    StructCtor _ _ -> doNotSupportError "structs"
    StructField _ _ _ -> doNotSupportError "structs"

    -- Strings
    StringAppend _ _ -> doNotSupportError "strings"
    StringContains _ _ -> doNotSupportError "strings"
    StringIndexOf _ _ _ -> doNotSupportError "strings"
    StringIsPrefixOf _ _ -> doNotSupportError "strings"
    StringIsSuffixOf _ _ -> doNotSupportError "strings"
    StringLength _ -> doNotSupportError "strings"
    StringSubstring _ _ _ _ -> doNotSupportError "strings"

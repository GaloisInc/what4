{-
Module           : What4.Protocol.VerilogWriter.Backend
Copyright        : (c) Galois, Inc 2020
Maintainer       : Jennifer Paykin <jpaykin@galois.com>
License          : BSD3

Convert What4 expressions into the data types defined in the @What4.Protocol.VerilogWriter.AST@ module.
-}
{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, ScopedTypeVariables, RankNTypes,
  TypeApplications, PolyKinds, DataKinds, ExplicitNamespaces, TypeOperators,
  LambdaCase, FlexibleContexts #-}

module What4.Protocol.VerilogWriter.Backend
  where


import           Control.Monad (mapM, foldM)
import           Control.Monad.State (get)
import           Control.Monad.Except
import           Data.Kind (Type)
import qualified Data.Parameterized.TraversableFC as TC
import           Data.List.NonEmpty ( NonEmpty(..) )

import           Data.Parameterized.Context


import qualified What4.Expr.BoolMap as BMap
import qualified What4.BaseTypes as WT
import           What4.Expr.Builder
import qualified What4.SemiRing as SR
import qualified What4.Expr.WeightedSum as WS
import qualified What4.Expr.UnaryBV as UBV

import What4.Protocol.VerilogWriter.AST


-- | Convert What4 expresssions into verilog expressions
exprToVerilogExpr' :: Expr n tp -> VerilogM n (IExp tp)
-- I don't think we care about the "flavor" of the semiring, since we just
-- produce a constant here.
exprToVerilogExpr' (SemiRingLiteral (SR.SemiRingBVRepr _ w) i _) = litBV w i
exprToVerilogExpr' (SemiRingLiteral _ _ _) = throwError "Unsupported literal type" -- TODO
exprToVerilogExpr' (BoolExpr b _)   = litBool b
exprToVerilogExpr' (StringExpr _ _) = throwError "Strings not supported in Verilog"
exprToVerilogExpr' (AppExpr app)    = appVerilogExpr app
exprToVerilogExpr' (NonceAppExpr n) = appExprVerilogExpr n
exprToVerilogExpr' (BoundVarExpr x) = do
    addInput tp name
    return $ Ident tp name
  where
    tp = bvarType x
    name = bvarIdentifier x

exprToVerilogExpr :: Expr n tp -> VerilogM n (IExp tp)
exprToVerilogExpr e = do
  cache <- vsExpCache <$> get
  idxCacheEval cache e (exprToVerilogExpr' e)

eqToVerilogExpr :: Expr n tp -> Expr n tp -> VerilogM n (IExp WT.BaseBoolType)
eqToVerilogExpr x y = do
  x' <- exprToVerilogExpr x
  y' <- exprToVerilogExpr y
  binop Eq x' y'

bvarIdentifier :: ExprBoundVar t tp -> Identifier
bvarIdentifier x = show (bvarName x)

appExprVerilogExpr :: NonceAppExpr n tp -> VerilogM n (IExp tp)
appExprVerilogExpr nae =
  case nonceExprApp nae of
    Forall _ _ -> throwError "No support for Forall expressions"
    Exists _ _ -> throwError "No support for Exists expressions"
    ArrayFromFn _ -> throwError "No support for Arrays"
    MapOverArrays _ _ _ -> throwError "No support for Arrays"
    ArrayTrueOnEntries _ _ -> throwError "No support for Arrays"
    FnApp f Empty -> do
      addInput tp name
      return $ Ident tp name
        where
          tp = symFnReturnType f
          name = show (symFnName f)
    -- TODO: inline defined functions?
    -- TODO: implement uninterpreted functions as uninterpreted functions
    -- FnApp f es | show f == "Prelude.Eq" -> throwError "nyi: Eq"
    FnApp f es -> throwError $ "No support for function applications: " ++ show f ++ show es
    Annotation _ _ _ -> throwError "Annotations not yet supported" -- TODO

toListFCM :: forall k (f :: k -> Type) t m a. (Monad m, TC.FoldableFC t)
          => (forall x. f x -> m a) -> forall x. t f x -> m [a]
toListFCM f t = TC.foldlMFC foo [] t
  where
    foo :: forall x. [a] -> f x -> m [a]
    foo l a = do a' <- f a
                 return (a' : l)

-- | As of now, all symbolic functions are just turned into verilog functions of
-- the same name, but it may be the case that some pre-defined uninterpreted
-- functions in What4 should be transformed into other operations in verilog. OR
-- maybe symbolic functions should be turned into module calls?
mkVerilogFn :: ExprSymFn t args ret -> String
mkVerilogFn f = show (symFnName f)

boolMapToExpr ::
  Bool ->
  Bool ->
  Binop WT.BaseBoolType WT.BaseBoolType ->
  BMap.BoolMap (Expr n) ->
  VerilogM n (IExp WT.BaseBoolType)
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

appVerilogExpr :: AppExpr n tp -> VerilogM n (IExp tp)
appVerilogExpr ae =
  case appExprApp ae of
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
    ConjPred es -> boolMapToExpr True False And es

    -- Semiring operations
    -- We only support bitvector semiring operations
    SemiRingSum s
      | SR.SemiRingBVRepr SR.BVArithRepr w <- WS.sumRepr s -> do
        let scalMult' c e = scalMult BVMul c =<< exprToVerilogExpr e
        WS.evalM (binop BVAdd) scalMult' (litBV w) s
      | SR.SemiRingBVRepr SR.BVBitsRepr w <- WS.sumRepr s ->
        let scalMult' c e = scalMult BVAnd c =<< exprToVerilogExpr e in
        WS.evalM (binop BVXor) scalMult' (litBV w) s
    SemiRingSum _ -> doNotSupportError "SemiRingSum (non-bitvectors)"
    SemiRingProd p
      | SR.SemiRingBVRepr SR.BVArithRepr w <- WS.prodRepr p ->
        WS.prodEvalM (binop BVMul) exprToVerilogExpr p >>= \case
          Nothing -> litBV w 1
          Just e  -> return e
      | SR.SemiRingBVRepr SR.BVBitsRepr w <- WS.prodRepr p ->
        WS.prodEvalM (binop BVAnd) exprToVerilogExpr p >>= \case
          Nothing -> litBV w (maxBV w)
          Just e  -> return e
    SemiRingProd _ -> doNotSupportError "SemiRingProd (non-bitvectors)"
    -- SemiRingLe only accounts for Nats, Integers, and Reals, not bitvectors
    SemiRingLe _ _ _ -> doNotSupportError "SemiRingLe"

    -- Arithmetic operations
    RealIsInteger _ -> doNotSupportError "RealIsInteger"
    NatDiv _ _ -> doNotSupportError "NatDiv"
    NatMod _ _ -> doNotSupportError "NatMod"

    IntDiv _ _ -> doNotSupportError "IntDiv"
    IntMod _ _ -> doNotSupportError "IntMod"
    IntAbs _ -> doNotSupportError "IntAbs"
    IntDivisible _ _ -> doNotSupportError "IntDivisible"

    RealDiv _ _ -> doNotSupportError "RealDiv"
    RealSqrt _ -> doNotSupportError "RealSqrt"

    -- Irrational numbers
    Pi -> doNotSupportError "Pi"

    RealSin _ -> doNotSupportError "RealSin"
    RealCos _ -> doNotSupportError "RealCos"
    RealATan2 _ _ -> doNotSupportError "RealATan2"
    RealSinh _ -> doNotSupportError "RealSinh"
    RealCosh _ -> doNotSupportError "RealCosh"

    RealExp _ -> doNotSupportError "RealExp"
    RealLog _ -> doNotSupportError "RealLog"

    -- Bitvector operations
    BVTestBit i e -> do v <- exprToVerilogExpr e
                        bit v (fromIntegral i)
    BVSlt _ _ -> doNotSupportError "BVSlt"
    BVUlt e1 e2 -> do e1' <- exprToVerilogExpr e1
                      e2' <- exprToVerilogExpr e2
                      binop Lt e1' e2'

    BVOrBits w bs ->
      do exprs <- mapM exprToVerilogExpr (bvOrToList bs)
         case exprs of
           [] -> litBV w 0
           e:es -> foldM (binop BVOr) e es
    BVUnaryTerm ubv -> UBV.sym_evaluate (litBV w) ite' ubv
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
                       e1 <- litBV len (maxBV len)
                       e2 <- litBV len 0
                       mux e e1 e2
    BVUdiv _   bv1 bv2 -> do bv1' <- exprToVerilogExpr bv1
                             bv2' <- exprToVerilogExpr bv2
                             binop BVDiv bv1' bv2'
    BVUrem _   bv1 bv2 -> do bv1' <- exprToVerilogExpr bv1
                             bv2' <- exprToVerilogExpr bv2
                             binop BVRem bv1' bv2'
    BVSdiv _   _   _   -> doNotSupportError "BVSdiv"
    BVSrem _   _   _   -> doNotSupportError "BVSrem"
    BVShl  _   bv1 bv2 -> do e1 <- exprToVerilogExpr bv1
                             e2 <- exprToVerilogExpr bv2
                             binop BVShiftL e1 e2
    BVLshr _   bv1 bv2 -> do e1 <- exprToVerilogExpr bv1
                             e2 <- exprToVerilogExpr bv2
                             binop BVShiftR e1 e2
    BVAshr _   bv1 bv2 -> do e1 <- exprToVerilogExpr bv1
                             e2 <- exprToVerilogExpr bv2
                             binop BVShiftRA e1 e2
    BVRol  _ _  _ -> doNotSupportError "BVRol"
    BVRor  _ _  _ -> doNotSupportError "BVRor"
    BVZext _ _ -> doNotSupportError "BVZext"
    BVSext _ _ -> doNotSupportError "BVSext"
    BVPopcount _ _ -> doNotSupportError "BVPopcount"
    BVCountTrailingZeros _ _ -> doNotSupportError "BVCountTrailingZeros"
    BVCountLeadingZeros  _ _ -> doNotSupportError "BVCountLeadingZeros"

    -- Float operations
    FloatPZero _ -> doNotSupportError "Floats"
    FloatNZero _ -> doNotSupportError "Floats"
    FloatNaN _ -> doNotSupportError "Floats"
    FloatPInf _ -> doNotSupportError "Floats"
    FloatNInf _ -> doNotSupportError "Floats"
    FloatNeg _ _ -> doNotSupportError "Floats"
    FloatAbs _ _ -> doNotSupportError "Floats"
    FloatSqrt _ _ _ -> doNotSupportError "Floats"
    FloatAdd  _ _ _ _ -> doNotSupportError "Floats"
    FloatSub  _ _ _ _ -> doNotSupportError "Floats"
    FloatMul  _ _ _ _ -> doNotSupportError "Floats"
    FloatDiv _ _ _ _ -> doNotSupportError "Floats"
    FloatRem _ _ _ -> doNotSupportError "Floats"
    FloatMin _ _ _ -> doNotSupportError "Floats"
    FloatMax _ _ _ -> doNotSupportError "Floats"
    FloatFMA _ _ _ _ _ -> doNotSupportError "Floats"
    FloatFpEq _ _ -> doNotSupportError "Floats"
    FloatFpNe _ _ -> doNotSupportError "Floats"
    FloatLe _ _ -> doNotSupportError "Floats"
    FloatLt _ _ -> doNotSupportError "Floats"

    FloatIsNaN _ -> doNotSupportError "Floats"
    FloatIsInf _ -> doNotSupportError "Floats"
    FloatIsZero _ -> doNotSupportError "Floats"
    FloatIsPos _ -> doNotSupportError "Floats"
    FloatIsNeg _ -> doNotSupportError "Floats"
    FloatIsSubnorm _ -> doNotSupportError "Floats"
    FloatIsNorm _ -> doNotSupportError "Floats"

    FloatCast _ _ _ -> doNotSupportError "Floats"
    FloatRound _ _ _ -> doNotSupportError "Floats"
    FloatFromBinary _ _ -> doNotSupportError "Floats"
    FloatToBinary _ _ -> doNotSupportError "Floats"
    BVToFloat _ _ _ -> doNotSupportError "Floats"
    SBVToFloat _ _ _ -> doNotSupportError "Floats"
    RealToFloat _ _ _ -> doNotSupportError "Floats"
    FloatToBV _ _ _ -> doNotSupportError "Floats"
    FloatToSBV _ _ _ -> doNotSupportError "Floats"
    FloatToReal _ -> doNotSupportError "Floats"

    -- Array operations
    ArrayMap _ _ _ _ -> doNotSupportError "Arrays"
    ConstantArray _ _ _ -> doNotSupportError "Arrays"
    UpdateArray _ _ _ _ _ -> doNotSupportError "Arrays"
    SelectArray _ _ _ -> doNotSupportError "Arrays"

    -- Conversions
    NatToInteger _ -> doNotSupportError "NatToInteger"
    IntegerToNat _ -> doNotSupportError "IntegerToNat"
    IntegerToReal _ -> doNotSupportError "IntegerToReal"
    RealToInteger _ -> doNotSupportError "RealToInteger"
    BVToNat _ -> doNotSupportError "BVToNat"
    BVToInteger _ -> doNotSupportError "BVToInteger"
    SBVToInteger _ -> doNotSupportError "SBVToInteger"
    IntegerToBV _ _ -> doNotSupportError "IntegerToBV"
    RoundReal _ -> doNotSupportError "RoundReal"
    FloorReal _ -> doNotSupportError "FloorReal"
    CeilReal _ -> doNotSupportError "CeilReal"

    -- Complex operations
    Cplx _ -> doNotSupportError "Complex numbers"
    RealPart _ -> doNotSupportError "Complex numbers"
    ImagPart _ -> doNotSupportError "Complex Numbers"

    -- Structs
    StructCtor _ _ -> doNotSupportError "Structs"
    StructField _ _ _ -> doNotSupportError "Structs"

    -- Strings
    StringAppend _ _ -> doNotSupportError "Strings"
    StringContains _ _ -> doNotSupportError "Strings"
    StringIndexOf _ _ _ -> doNotSupportError "Strings"
    StringIsPrefixOf _ _ -> doNotSupportError "Strings"
    StringIsSuffixOf _ _ -> doNotSupportError "Strings"
    StringLength _ -> doNotSupportError "Strings"
    StringSubstring _ _ _ _ -> doNotSupportError "Strings"

  where
    doNotSupportError cstr = throwError $ "Do not support constructor " ++ cstr

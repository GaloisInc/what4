{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

{-|
Module      : Who2.Protocol.SMTLib2
Description : Serialization of Who2 expressions to SMT-Lib2 format
Copyright   : (c) Galois, Inc 2026
License     : BSD3
Maintainer  : langston@galois.com

This module provides conversion functions for 'ES.SymExpr' to SMT-Lib2
'SMT2.Term's. It provides direct conversion without caching, suitable for
one-time serialization of expressions for debugging, testing, or offline
solving.
-}

module Who2.Protocol.SMTLib2
  ( -- * Entry points
    mkSMTTerm
  , mkSMTTermWithDecls
  , mkExpr
  , mkFormula
    -- * Type conversion
  , baseTypeToSort
    -- * Internal dispatchers (exported for testing)
  , mkApp
  , mkBVExpr
  , mkLogicExpr
  ) where

import qualified Data.BitVector.Sized as BV
import Data.Bits ((.&.), complement, xor)
import Data.Coerce (coerce)
import Data.IORef (IORef, newIORef, readIORef, modifyIORef')
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Nonce (Nonce, indexValue)
import Data.Parameterized.NatRepr (natValue, NatRepr, type (<=))
import Data.Parameterized.TraversableFC (fmapFC, toListFC)
import qualified Data.Text as Text
import qualified Data.Text.Lazy as Text.Lazy
import qualified Data.Text.Lazy.Builder as Builder

import qualified What4.BaseTypes as BT
import qualified What4.Expr as WE
import qualified What4.Expr.App as WEA
import qualified What4.Protocol.SMTLib2.Syntax as SMT2
import qualified What4.Symbol as WS
import qualified What4.Utils.AbstractDomains as AD
import qualified What4.Utils.BVDomain as BVD
import What4.Utils.BVDomain (BVDomain)
import qualified What4.Utils.BVDomain.Bitwise as B

import qualified Who2.Expr as E
import qualified Who2.Expr.App as EA
import qualified Who2.Expr.BV as EBV
import qualified Who2.Expr.Logic as EL
import qualified Who2.Expr.PolarizedBloomSeq as PBS
import qualified Who2.Expr.SymExpr as ES
import qualified Who2.Expr.SymFn as ESF
import qualified Who2.Expr.Views as EV
import qualified Who2.Expr.SemiRing.Product as SRP
import qualified Who2.Expr.SemiRing.Sum as SRS

------------------------------------------------------------------------
-- Flags

-- | Emit abstract domain constraints for bound variables.
--
-- When True, bound variables (free variables in formulas) are wrapped with
-- @bvand@/@bvor@ to encode known bits from abstract domain analysis. This
-- provides solver hints at minimal cost (linear in number of variables).
emitAbstractDomainConstraintsForBoundVars :: Bool
emitAbstractDomainConstraintsForBoundVars = False
{-# INLINE emitAbstractDomainConstraintsForBoundVars #-}

-- | Emit abstract domain constraints for all bitvector expressions.
--
-- When @True@, ALL bitvector expressions are wrapped with @bvand@/@bvor@
-- to encode known bits. WARNING: This might be very expensive, needs more
-- benchmarking.
emitAbstractDomainConstraintsForAllBV :: Bool
emitAbstractDomainConstraintsForAllBV = False
{-# INLINE emitAbstractDomainConstraintsForAllBV #-}

------------------------------------------------------------------------
-- Variable Cache

-- | Cache for mapping nonces to generated variable names
type VarCache t = IORef (Map.Map Integer Text.Text)

-- | Function declaration information
data FnDecl = FnDecl
  { fdName :: !Text.Text
  , fdArgSorts :: ![SMT2.Sort]
  , fdRetSort :: !SMT2.Sort
  }

-- | Cache for tracking function declarations
type FnCache t = IORef (Map.Map Integer FnDecl)

-- | Combined cache for serialization state
data SerializerCache t = SerializerCache
  { scVarCache :: !(VarCache t)
  , scFnCache :: !(FnCache t)
  }

-- | Create a new empty variable cache
newVarCache :: IO (VarCache t)
newVarCache = newIORef Map.empty

-- | Create a new empty function cache
newFnCache :: IO (FnCache t)
newFnCache = newIORef Map.empty

-- | Create a new serializer cache
newSerializerCache :: IO (SerializerCache t)
newSerializerCache = SerializerCache <$> newVarCache <*> newFnCache

-- | Look up or generate a variable name for a nonce
lookupOrGenVarName :: SerializerCache t -> Nonce t tp -> BT.BaseTypeRepr tp -> IO SMT2.Term
lookupOrGenVarName cache nonce tp = do
  cacheMap <- readIORef (scVarCache cache)
  let nonceIdx = toInteger (indexValue nonce)
  case Map.lookup nonceIdx cacheMap of
    Just name -> return $ SMT2.T (Builder.fromText name)
    Nothing -> do
      let name = generateVarName nonce tp
      modifyIORef' (scVarCache cache) (Map.insert nonceIdx name)
      return $ SMT2.T (Builder.fromText name)

-- | Generate a readable variable name based on nonce and type
generateVarName :: Nonce t tp -> BT.BaseTypeRepr tp -> Text.Text
generateVarName nonce tp =
  let nonceStr = Text.pack $ show (indexValue nonce)
  in case tp of
    BT.BaseBoolRepr -> Text.pack "b_" <> nonceStr
    BT.BaseBVRepr w -> Text.pack "bv" <> Text.pack (show (natValue w)) <> Text.pack "_" <> nonceStr
    _ -> Text.pack "v_" <> nonceStr

------------------------------------------------------------------------
-- Type Mapping

-- | Get SMT sort from BaseTypeRepr
baseTypeToSort :: BT.BaseTypeRepr tp -> SMT2.Sort
baseTypeToSort BT.BaseBoolRepr = SMT2.boolSort
baseTypeToSort (BT.BaseBVRepr w) = SMT2.bvSort (natValue w)
baseTypeToSort tp = error $ "Who2.Protocol.SMTLib2.baseTypeToSort: unsupported type " ++ show tp

------------------------------------------------------------------------
-- Main Entry Points

-- | Convert a Who2 SymExpr to an SMT-Lib2 Term.
-- This is the main entry point for serialization.
mkSMTTerm ::
  ES.SymExpr t tp ->
  IO SMT2.Term
mkSMTTerm (ES.SymExpr expr) = do
  cache <- newSerializerCache
  mkExprWithCache cache expr

-- | Convert a Who2 SymExpr to an SMT-Lib2 Term with function and variable declarations.
-- Returns (declarations, term) where declarations include both functions and variables.
mkSMTTermWithDecls ::
  ES.SymExpr t tp ->
  IO ([Text.Text], SMT2.Term)
mkSMTTermWithDecls (ES.SymExpr expr) = do
  cache <- newSerializerCache
  term <- mkExprWithCache cache expr
  fnDecls <- getFunctionDeclarations cache
  varDecls <- getVariableDeclarations cache
  let allDecls = varDecls ++ fnDecls
  return (allDecls, term)

-- | Extract variable declarations from cache as SMT-Lib2 declare-const commands
getVariableDeclarations :: SerializerCache t -> IO [Text.Text]
getVariableDeclarations cache = do
  varMap <- readIORef (scVarCache cache)
  let varList = Map.toList varMap
  return $ map renderVarDecl varList
  where
    renderVarDecl :: (Integer, Text.Text) -> Text.Text
    renderVarDecl (_idx, name) =
      -- We need to determine the type from the variable name prefix
      -- bv8_, bv16_, etc. for bitvectors, b_ for booleans
      let sort = inferSortFromName name
          sortText = Text.Lazy.toStrict $ Builder.toLazyText $ SMT2.unSort sort
      in Text.pack "(declare-const " <> name <> Text.pack " " <> sortText <> Text.pack ")"

    -- Infer sort from variable name (hacky but works for our naming scheme)
    inferSortFromName :: Text.Text -> SMT2.Sort
    inferSortFromName name
      | Text.pack "b_" `Text.isPrefixOf` name = SMT2.boolSort
      | Text.pack "bv" `Text.isPrefixOf` name =
          let rest = Text.drop 2 name
              widthStr = Text.takeWhile (/= '_') rest
          in case reads (Text.unpack widthStr) of
               [(w, "")] -> SMT2.bvSort w
               _ -> error $ "Failed to parse bitvector width from: " ++ Text.unpack name
      | otherwise = error $ "Unknown variable name format: " ++ Text.unpack name

-- | Extract function declarations from cache as SMT-Lib2 declare-fun commands
getFunctionDeclarations :: SerializerCache t -> IO [Text.Text]
getFunctionDeclarations cache = do
  fnMap <- readIORef (scFnCache cache)
  let declList = Map.elems fnMap
  return $ map renderFnDecl declList
  where
    renderFnDecl :: FnDecl -> Text.Text
    renderFnDecl (FnDecl name argSorts retSort) =
      let sortToText s = Text.Lazy.toStrict $ Builder.toLazyText $ SMT2.unSort s
          argSortsText = Text.intercalate (Text.pack " ") (map sortToText argSorts)
          retSortText = sortToText retSort
          argsSection = if null argSorts
                        then Text.pack ""
                        else Text.pack "(" <> argSortsText <> Text.pack ")"
      in Text.pack "(declare-fun " <> name <> Text.pack " " <> argsSection <> Text.pack " " <> retSortText <> Text.pack ")"

-- | Convert a Who2 Expr to a Term with serializer cache
mkExprWithCache ::
  SerializerCache t ->
  E.Expr t (EA.App t) tp ->
  IO SMT2.Term
mkExprWithCache cache expr = do
  baseTerm <- mkAppWithCache cache (E.eApp expr)
  if emitAbstractDomainConstraintsForAllBV
    then return $ applyExprConstraints (E.baseType expr) (E.eAbsVal expr) baseTerm
    else return baseTerm

-- | Convert a Who2 Expr to a Term (creates new cache)
mkExpr ::
  E.Expr t (EA.App t) tp ->
  IO SMT2.Term
mkExpr expr = do
  cache <- newSerializerCache
  mkExprWithCache cache expr

-- | Convert a Who2 boolean expression to a Term (alias for mkSMTTerm)
mkFormula ::
  ES.SymExpr t BT.BaseBoolType ->
  IO SMT2.Term
mkFormula = mkSMTTerm

------------------------------------------------------------------------
-- App Dispatcher

-- | Dispatch on App constructor to appropriate handler
mkAppWithCache ::
  SerializerCache t ->
  EA.App t (E.Expr t (EA.App t)) tp ->
  IO SMT2.Term
mkAppWithCache cache = \case
  EA.BoundVarApp var -> mkBoundVar cache var
  EA.BVApp bvExpr -> mkBVExprWithCache cache bvExpr
  EA.LogicApp logicExpr -> mkLogicExprWithCache cache logicExpr
  EA.FnApp fn args -> mkFnApp cache fn args

-- | Dispatch without cache (exported for testing)
mkApp ::
  EA.App t (E.Expr t (EA.App t)) tp ->
  IO SMT2.Term
mkApp app = do
  cache <- newSerializerCache
  mkAppWithCache cache app

-- | Convert a bound variable to a Term
mkBoundVar ::
  SerializerCache t ->
  WE.ExprBoundVar t tp ->
  IO SMT2.Term
mkBoundVar cache var = do
  baseTerm <- lookupOrGenVarName cache (WE.bvarId var) (WEA.bvarType var)
  if emitAbstractDomainConstraintsForBoundVars
    then return $ applyBoundVarConstraints
                    (WEA.bvarType var)
                    (WEA.bvarAbstractValue var)
                    baseTerm
    else return baseTerm

------------------------------------------------------------------------
-- Bitvector Operations

-- | Convert a BVExpr to a Term with cache
mkBVExprWithCache ::
  SerializerCache t ->
  EBV.BVExpr (E.Expr t (EA.App t)) tp ->
  IO SMT2.Term
mkBVExprWithCache cache = \case
  EBV.BVLit w bv -> return $ SMT2.bvhexadecimal w bv

  EBV.BVAdd w ws -> do
    -- Serialize weighted sum as additions and multiplications
    let terms = SRS.toTerms ws
        offset = SRS.sumOffset ws
    -- Start with the offset if non-zero
    let offsetTerm = if offset == BV.zero w
                     then Nothing
                     else Just (SMT2.bvhexadecimal w offset)
    -- Create terms for each coefficient * variable
    scaledTerms <- mapM (\(expr, coeff) -> do
                           exprTerm <- mkExprWithCache cache expr
                           if coeff == BV.mkBV w 1
                           then return exprTerm
                           else do
                             let coeffTerm = SMT2.bvhexadecimal w coeff
                             return $ SMT2.bvmul exprTerm [coeffTerm])
                        terms
    -- Combine all terms with bvadd
    case (offsetTerm, scaledTerms) of
      (Nothing, []) -> return $ SMT2.bvhexadecimal w (BV.zero w)
      (Nothing, t:ts) -> return $ foldl (\acc t' -> SMT2.bvadd acc [t']) t ts
      (Just off, []) -> return off
      (Just off, t:ts) -> return $ foldl (\acc t' -> SMT2.bvadd acc [t']) off (t:ts)

  EBV.BVSub _ x y -> do
    xTerm <- mkExprWithCache cache x
    yTerm <- mkExprWithCache cache y
    return $ SMT2.bvsub xTerm yTerm

  EBV.BVMul _ wp -> do
    let terms = SRP.toTerms wp
    termList <- mapM (\(x, expn) -> do
                       xTerm <- mkExprWithCache cache x
                       return $ replicate (fromIntegral expn) xTerm) terms
    case concat termList of
      [] -> return $ SMT2.numeral 1  -- empty product = 1
      (t:ts) -> return $ SMT2.bvmul t ts

  EBV.BVNeg _ x -> do
    xTerm <- mkExprWithCache cache x
    return $ SMT2.bvneg xTerm

  EBV.BVAndBits _ pbs -> do
    let posElems = coerce $ PBS.toListPos pbs
        negElems = coerce $ PBS.toListNeg pbs
    posTerms <- mapM (mkExprWithCache cache) posElems
    negTerms <- mapM (mkExprWithCache cache) negElems
    let negTerms' = map SMT2.bvnot negTerms
        allTerms = posTerms ++ negTerms'
    case allTerms of
      [] -> error "BVAndBits: empty PolarizedBloomSeq"
      (t:ts) -> return $ SMT2.bvand t ts

  EBV.BVOrBits _ pbs -> do
    let posElems = coerce $ PBS.toListPos pbs
        negElems = coerce $ PBS.toListNeg pbs
    posTerms <- mapM (mkExprWithCache cache) posElems
    negTerms <- mapM (mkExprWithCache cache) negElems
    let negTerms' = map SMT2.bvnot negTerms
        allTerms = posTerms ++ negTerms'
    case allTerms of
      [] -> error "BVOrBits: empty PolarizedBloomSeq"
      (t:ts) -> return $ SMT2.bvor t ts

  EBV.BVXorBits _ x y -> do
    xTerm <- mkExprWithCache cache x
    yTerm <- mkExprWithCache cache y
    return $ SMT2.bvxor xTerm [yTerm]

  EBV.BVNotBits _ x -> do
    xTerm <- mkExprWithCache cache x
    return $ SMT2.bvnot xTerm

  EBV.BVConcat _ _ x y -> do
    xTerm <- mkExprWithCache cache x
    yTerm <- mkExprWithCache cache y
    return $ SMT2.concat xTerm yTerm

  EBV.BVSelect i n _ x -> do
    xTerm <- mkExprWithCache cache x
    let hi = natValue i + natValue n - 1
    let lo = natValue i
    return $ SMT2.extract hi lo xTerm

  EBV.BVZext targetWidth sourceWidth x -> do
    xTerm <- mkExprWithCache cache x
    let extendBy = toInteger (natValue targetWidth - natValue sourceWidth)
    return $ SMT2.bvzeroExtend extendBy xTerm

  EBV.BVSext targetWidth sourceWidth x -> do
    xTerm <- mkExprWithCache cache x
    let extendBy = toInteger (natValue targetWidth - natValue sourceWidth)
    return $ SMT2.bvsignExtend extendBy xTerm

  EBV.BVShl _ x y -> do
    xTerm <- mkExprWithCache cache x
    yTerm <- mkExprWithCache cache y
    return $ SMT2.bvshl xTerm yTerm

  EBV.BVLshr _ x y -> do
    xTerm <- mkExprWithCache cache x
    yTerm <- mkExprWithCache cache y
    return $ SMT2.bvlshr xTerm yTerm

  EBV.BVAshr _ x y -> do
    xTerm <- mkExprWithCache cache x
    yTerm <- mkExprWithCache cache y
    return $ SMT2.bvashr xTerm yTerm

  EBV.BVUdiv _ x y -> do
    xTerm <- mkExprWithCache cache x
    yTerm <- mkExprWithCache cache y
    return $ SMT2.bvudiv xTerm yTerm

  EBV.BVUrem _ x y -> do
    xTerm <- mkExprWithCache cache x
    yTerm <- mkExprWithCache cache y
    return $ SMT2.bvurem xTerm yTerm

  EBV.BVSdiv _ x y -> do
    xTerm <- mkExprWithCache cache x
    yTerm <- mkExprWithCache cache y
    return $ SMT2.bvsdiv xTerm yTerm

  EBV.BVSrem _ x y -> do
    xTerm <- mkExprWithCache cache x
    yTerm <- mkExprWithCache cache y
    return $ SMT2.bvsrem xTerm yTerm

  -- Rotations: use native SMT-Lib2 rotate_left/rotate_right when amount is literal
  EBV.BVRol w x y -> do
    xTerm <- mkExprWithCache cache x
    case EV.asBVLit y of
      Just (_w, bv) -> do
        -- Use native rotate_left with constant amount
        let rotAmt = toInteger (BV.asNatural bv) `mod` toInteger (natValue w)
        let op = Builder.fromString "(_ rotate_left " <> Builder.fromString (show rotAmt) <> Builder.fromString ")"
        return $ SMT2.T $ Builder.fromString "(" <> op <> Builder.fromString " " <> SMT2.renderTerm xTerm <> Builder.fromString ")"
      Nothing -> do
        -- Synthesize: (x << y) | (x >> (w - y))
        yTerm <- mkExprWithCache cache y
        let widthLit = SMT2.bvdecimal w (BV.mkBV w (toInteger (natValue w)))
        let shiftAmt = SMT2.bvsub widthLit yTerm
        let leftPart = SMT2.bvshl xTerm yTerm
        let rightPart = SMT2.bvlshr xTerm shiftAmt
        return $ SMT2.bvor leftPart [rightPart]

  EBV.BVRor w x y -> do
    xTerm <- mkExprWithCache cache x
    case EV.asBVLit y of
      Just (_w, bv) -> do
        -- Use native rotate_right with constant amount
        let rotAmt = toInteger (BV.asNatural bv) `mod` toInteger (natValue w)
        let op = Builder.fromString "(_ rotate_right " <> Builder.fromString (show rotAmt) <> Builder.fromString ")"
        return $ SMT2.T $ Builder.fromString "(" <> op <> Builder.fromString " " <> SMT2.renderTerm xTerm <> Builder.fromString ")"
      Nothing -> do
        -- Synthesize: (x >> y) | (x << (w - y))
        yTerm <- mkExprWithCache cache y
        let widthLit = SMT2.bvdecimal w (BV.mkBV w (toInteger (natValue w)))
        let shiftAmt = SMT2.bvsub widthLit yTerm
        let rightPart = SMT2.bvlshr xTerm yTerm
        let leftPart = SMT2.bvshl xTerm shiftAmt
        return $ SMT2.bvor rightPart [leftPart]

-- | Convert BVExpr without cache (exported for testing)
mkBVExpr ::
  EBV.BVExpr (E.Expr t (EA.App t)) tp ->
  IO SMT2.Term
mkBVExpr bvExpr = do
  cache <- newSerializerCache
  mkBVExprWithCache cache bvExpr

-- | Compute max unsigned value for a bitvector width (all bits set to 1).
maxUnsigned :: (1 <= w) => NatRepr w -> Integer
maxUnsigned w = 2 ^ natValue w - 1

-- | Apply abstract domain constraints to a bitvector term.
--
-- Wraps the term with bvand/bvor to encode known-0 and known-1 bits from
-- the abstract domain. Returns the original term unchanged if:
--   - All bits are unknown (no precision to encode)
--   - Domain is a singleton (term should already be concrete)
applyBVAbstractConstraints ::
  forall w.
  (1 <= w) =>
  NatRepr w ->
  BVDomain w ->
  SMT2.Term ->
  SMT2.Term
applyBVAbstractConstraints w domain baseTerm
  -- If domain is singleton, term already encodes full precision
  | Just _ <- BVD.asSingleton domain = baseTerm
  | otherwise =
      let mask = maxUnsigned w
          (lo, hi) = B.bitbounds (BVD.asBitwiseDomain domain)
          unknown = lo `xor` hi
          known1 = hi .&. complement unknown  -- bits that MUST be 1
          known0_mask = complement lo         -- inverted: 1s where bits CAN be 1
      in if unknown == mask
         then baseTerm  -- No known bits, skip constraints
         else
           -- Encode: (bvand (bvor baseTerm known1) known0_mask)
           -- The bvor forces known-1 bits to 1
           -- The bvand forces known-0 bits to 0
           let known1_term = SMT2.bvhexadecimal w (BV.mkBV w known1)
               known0_term = SMT2.bvhexadecimal w (BV.mkBV w known0_mask)
               withKnown1 = SMT2.bvor baseTerm [known1_term]
           in SMT2.bvand withKnown1 [known0_term]

-- | Apply abstract domain constraints from a bound variable's abstract value.
--
-- Only applies to bitvector types. Returns original term for other types.
-- Handles the case where bvarAbstractValue is Nothing (no constraints applied).
applyBoundVarConstraints ::
  forall tp.
  BT.BaseTypeRepr tp ->
  Maybe (AD.AbstractValue tp) ->
  SMT2.Term ->
  SMT2.Term
applyBoundVarConstraints (BT.BaseBVRepr w) (Just absVal) baseTerm =
  applyBVAbstractConstraints w absVal baseTerm
applyBoundVarConstraints _ _ baseTerm =
  baseTerm  -- No constraints for non-BV types or missing abstract values

-- | Apply abstract domain constraints from an expression's abstract value.
-- Only applies to bitvector types. Returns original term for other types.
applyExprConstraints ::
  forall tp.
  BT.BaseTypeRepr tp ->
  AD.AbstractValue tp ->
  SMT2.Term ->
  SMT2.Term
applyExprConstraints (BT.BaseBVRepr w) absVal baseTerm =
  applyBVAbstractConstraints w absVal baseTerm
applyExprConstraints _ _ baseTerm =
  baseTerm  -- Only apply to bitvectors

------------------------------------------------------------------------
-- Logic Operations

-- | Convert a LogicExpr to a Term with cache
mkLogicExprWithCache ::
  SerializerCache t ->
  EL.LogicExpr (E.Expr t (EA.App t)) tp ->
  IO SMT2.Term
mkLogicExprWithCache cache = \case
  EL.TruePred -> return SMT2.true

  EL.FalsePred -> return SMT2.false

  EL.EqPred x y -> do
    xTerm <- mkExprWithCache cache x
    yTerm <- mkExprWithCache cache y
    return $ SMT2.eq [xTerm, yTerm]

  EL.AndPred pbs -> do
    let posElems = coerce $ PBS.toListPos pbs
        negElems = coerce $ PBS.toListNeg pbs
    posTerms <- mapM (mkExprWithCache cache) posElems
    negTerms <- mapM (mkExprWithCache cache) negElems
    let negTerms' = map SMT2.not negTerms
        allTerms = posTerms ++ negTerms'
    case allTerms of
      [] -> return SMT2.true
      _ -> return $ SMT2.and allTerms

  EL.NotPred x -> do
    xTerm <- mkExprWithCache cache x
    return $ SMT2.not xTerm

  EL.OrPred pbs -> do
    let posElems = coerce $ PBS.toListPos pbs
        negElems = coerce $ PBS.toListNeg pbs
    posTerms <- mapM (mkExprWithCache cache) posElems
    negTerms <- mapM (mkExprWithCache cache) negElems
    let negTerms' = map SMT2.not negTerms
        allTerms = posTerms ++ negTerms'
    case allTerms of
      [] -> return SMT2.false
      _ -> return $ SMT2.or allTerms

  EL.Ite c t f -> do
    cTerm <- mkExprWithCache cache c
    tTerm <- mkExprWithCache cache t
    fTerm <- mkExprWithCache cache f
    return $ SMT2.ite cTerm tTerm fTerm

  EL.BVUlt _ x y -> do
    xTerm <- mkExprWithCache cache x
    yTerm <- mkExprWithCache cache y
    return $ SMT2.bvult xTerm yTerm

  EL.BVUle _ x y -> do
    xTerm <- mkExprWithCache cache x
    yTerm <- mkExprWithCache cache y
    return $ SMT2.bvule xTerm yTerm

  EL.BVSlt _ x y -> do
    xTerm <- mkExprWithCache cache x
    yTerm <- mkExprWithCache cache y
    return $ SMT2.bvslt xTerm yTerm

  EL.BVSle _ x y -> do
    xTerm <- mkExprWithCache cache x
    yTerm <- mkExprWithCache cache y
    return $ SMT2.bvsle xTerm yTerm

-- | Convert LogicExpr without cache (exported for testing)
mkLogicExpr ::
  EL.LogicExpr (E.Expr t (EA.App t)) tp ->
  IO SMT2.Term
mkLogicExpr logicExpr = do
  cache <- newSerializerCache
  mkLogicExprWithCache cache logicExpr

------------------------------------------------------------------------
-- Function Application

-- | Get function name from SymFn
getFnName :: ESF.SymFn t f args ret -> Text.Text
getFnName fn = WS.solverSymbolAsText (ESF.symFnName fn)

-- | Convert argument types to SMT sorts
argTypesToSorts :: Ctx.Assignment BT.BaseTypeRepr args -> [SMT2.Sort]
argTypesToSorts = toListFC baseTypeToSort

-- | Check if function has been declared, and store its declaration
ensureFnDeclared :: SerializerCache t -> ESF.SymFn t f args ret -> IO ()
ensureFnDeclared cache fn = do
  let nonceIdx = toInteger $ indexValue $ ESF.symFnId fn
  fnMap <- readIORef (scFnCache cache)
  case Map.lookup nonceIdx fnMap of
    Just _ -> return ()  -- Already declared
    Nothing -> do
      -- Store function declaration information
      let fnName = getFnName fn
      let (argTypes, retType) = case ESF.symFnInfo fn of
            ESF.UninterpFnInfo args ret -> (args, ret)
            ESF.DefinedFnInfo vars _ _ ret -> (fmapFC WEA.bvarType vars, ret)
      let argSorts = argTypesToSorts argTypes
      let retSort = baseTypeToSort retType
      let decl = FnDecl { fdName = fnName, fdArgSorts = argSorts, fdRetSort = retSort }
      modifyIORef' (scFnCache cache) (Map.insert nonceIdx decl)

-- | Convert a function application to a Term
mkFnApp ::
  forall t args ret.
  SerializerCache t ->
  ESF.SymFn t (E.Expr t (EA.App t)) args ret ->
  Ctx.Assignment (E.Expr t (EA.App t)) args ->
  IO SMT2.Term
mkFnApp cache fn args = do
  -- Ensure the function is declared
  ensureFnDeclared cache fn

  -- Build function application: (fn_name arg1 arg2 ...)
  let fnName = getFnName fn

  -- Convert arguments: toListFC gives [IO Term], sequence gives IO [Term]
  argTerms <- sequence (toListFC (mkExprWithCache cache) args)

  return $ case argTerms of
    [] -> SMT2.T (Builder.fromText fnName)  -- Nullary function is just the name
    _  -> SMT2.T $ Builder.fromString "("
                <> Builder.fromText fnName
                <> mconcat [Builder.fromString " " <> SMT2.renderTerm arg | arg <- argTerms]
                <> Builder.fromString ")"

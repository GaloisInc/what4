{-
Module           : What4.Protocol.VerilogWriter.AST
Copyright        : (c) Galois, Inc 2020
Maintainer       : Jennifer Paykin <jpaykin@galois.com>
License          : BSD3

An intermediate AST to use for generating Verilog modules from What4 expressions.
-}
{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, ScopedTypeVariables,
  TypeApplications, PolyKinds, DataKinds, ExplicitNamespaces, TypeOperators #-}

module What4.Protocol.VerilogWriter.AST
  where

import qualified Data.BitVector.Sized as BV
import qualified Data.Map as Map
import           Control.Monad.Except
import           Control.Monad.State (MonadState(), StateT(..), get, put, modify)

import qualified What4.BaseTypes as WT
import           What4.Expr.Builder
import           Data.Parameterized.Classes (OrderingF(..), compareF)
import           Data.Parameterized.Some (Some(..))
import           Data.Parameterized.Pair
import           GHC.TypeNats ( type (<=) )

type Identifier = String

-- | A type for Verilog binary operators that enforces well-typedness,
-- including bitvector size constraints.
data Binop (inTp :: WT.BaseType) (outTp :: WT.BaseType) where
  And :: Binop WT.BaseBoolType WT.BaseBoolType
  Or  :: Binop WT.BaseBoolType WT.BaseBoolType
  Xor :: Binop WT.BaseBoolType WT.BaseBoolType

  Eq :: Binop tp WT.BaseBoolType
  Ne :: Binop tp WT.BaseBoolType
  Lt :: Binop (WT.BaseBVType w) WT.BaseBoolType
  Le :: Binop (WT.BaseBVType w) WT.BaseBoolType

  BVAnd :: Binop (WT.BaseBVType w) (WT.BaseBVType w)
  BVOr  :: Binop (WT.BaseBVType w) (WT.BaseBVType w)
  BVXor :: Binop (WT.BaseBVType w) (WT.BaseBVType w)
  BVAdd :: Binop (WT.BaseBVType w) (WT.BaseBVType w)
  BVSub :: Binop (WT.BaseBVType w) (WT.BaseBVType w)
  BVMul :: Binop (WT.BaseBVType w) (WT.BaseBVType w)
  BVDiv :: Binop (WT.BaseBVType w) (WT.BaseBVType w)
  BVRem :: Binop (WT.BaseBVType w) (WT.BaseBVType w)
  BVPow :: Binop (WT.BaseBVType w) (WT.BaseBVType w)
  BVShiftL :: Binop (WT.BaseBVType w) (WT.BaseBVType w)
  BVShiftR :: Binop (WT.BaseBVType w) (WT.BaseBVType w)
  BVShiftRA :: Binop (WT.BaseBVType w) (WT.BaseBVType w)

binopType ::
  Binop inTp outTp ->
  WT.BaseTypeRepr inTp ->
  WT.BaseTypeRepr outTp
binopType And _ = WT.BaseBoolRepr
binopType Or  _ = WT.BaseBoolRepr
binopType Xor _ = WT.BaseBoolRepr
binopType Eq  _ = WT.BaseBoolRepr
binopType Ne  _ = WT.BaseBoolRepr
binopType Lt  _ = WT.BaseBoolRepr
binopType Le  _ = WT.BaseBoolRepr
binopType BVAnd  tp = tp
binopType BVOr  tp = tp
binopType BVXor tp = tp
binopType BVAdd tp = tp
binopType BVSub tp = tp
binopType BVMul tp = tp
binopType BVDiv tp = tp
binopType BVRem tp = tp
binopType BVPow tp = tp
binopType BVShiftL tp = tp
binopType BVShiftR tp = tp
binopType BVShiftRA tp = tp

-- | A type for Verilog unary operators that enforces well-typedness.
data Unop (tp :: WT.BaseType) where
  Not :: Unop WT.BaseBoolType
  BVNot :: Unop (WT.BaseBVType w)

-- | A type for Verilog expression names that enforces well-typedness.
-- This type exists essentially to pair a name and type to avoid needing
-- to repeat them and ensure that all uses of the name are well-typed.
data IExp (tp :: WT.BaseType) where
  Ident   :: WT.BaseTypeRepr tp -> Identifier -> IExp tp

iexpType :: IExp tp -> WT.BaseTypeRepr tp
iexpType (Ident tp _) = tp

data LHS = LHS Identifier | LHSBit Identifier Integer

-- | A type for Verilog expressions that enforces well-typedness,
-- including bitvector size constraints.
data Exp (tp :: WT.BaseType) where
  IExp :: IExp tp -> Exp tp
  Binop :: Binop inTp outTp -> IExp inTp -> IExp inTp -> Exp outTp
  Unop :: Unop tp -> IExp tp -> Exp tp
  BVRotateL :: WT.NatRepr w -> IExp tp -> BV.BV w -> Exp tp
  BVRotateR :: WT.NatRepr w -> IExp tp -> BV.BV w -> Exp tp
  Mux :: IExp WT.BaseBoolType -> IExp tp -> IExp tp -> Exp tp
  Bit :: IExp (WT.BaseBVType w)
      -> Integer
      -> Exp WT.BaseBoolType
  BitSelect :: (1 WT.<= len, start WT.+ len WT.<= w)
      => IExp (WT.BaseBVType w)
      -> WT.NatRepr start
      -> WT.NatRepr len
      -> Exp (WT.BaseBVType len)
  Concat :: 1 <= w
          => WT.NatRepr w -> [Some IExp] -> Exp (WT.BaseBVType w)
  BVLit   :: (1 <= w)
          => WT.NatRepr w -- the width
          -> BV.BV w -- the value
          -> Exp (WT.BaseBVType w)
  BoolLit :: Bool -> Exp WT.BaseBoolType

expType :: Exp tp -> WT.BaseTypeRepr tp
expType (IExp e) = iexpType e
expType (Binop op e1 _) = binopType op (iexpType e1)
expType (BVRotateL _ e _) = iexpType e
expType (BVRotateR _ e _) = iexpType e
expType (Unop _ e) = iexpType e
expType (Mux _ e1 _) = iexpType e1
expType (Bit _ _) = WT.BaseBoolRepr
expType (BitSelect _ _ n) = WT.BaseBVRepr n
expType (Concat w _) = WT.BaseBVRepr w
expType (BVLit w _) = WT.BaseBVRepr w
expType (BoolLit _) = WT.BaseBoolRepr


-- | Create a let binding, associating a name with an expression. In
-- Verilog, this is a new "wire".
mkLet :: Exp tp -> VerilogM sym n (IExp tp)
mkLet (IExp x) = return x
mkLet e = do
    let tp = expType e
    x <- addFreshWire tp False "x" e
    return (Ident tp x)

-- | Indicate than an expression name is signed. This causes arithmetic
-- operations involving this name to be interpreted as signed
-- operations.
signed :: IExp tp -> VerilogM sym n (IExp tp)
signed e = do
    let tp = iexpType e
    x <- addFreshWire tp True "x" (IExp e)
    return (Ident tp x)

-- | Apply a binary operation to two expressions and bind the result to
-- a new, returned name.
binop ::
  Binop inTp outTp ->
  IExp inTp -> IExp inTp ->
  VerilogM sym n (IExp outTp)
binop op e1 e2 = mkLet (Binop op e1 e2)

-- | A special binary operation for scalar multiplication. This avoids
-- the need to call `litBV` at every call site.
scalMult ::
  1 <= w =>
  WT.NatRepr w ->
  Binop (WT.BaseBVType w) (WT.BaseBVType w) ->
  BV.BV w ->
  IExp (WT.BaseBVType w) ->
  VerilogM sym n (IExp (WT.BaseBVType w))
scalMult w op n e = do
  n' <- litBV w n
  binop op n' e

-- | A wrapper around the BV type allowing it to be put into a map or
-- set. We use this to make sure we generate only one instance of each
-- distinct constant.
data BVConst = BVConst (Pair WT.NatRepr BV.BV)
  deriving (Eq)

instance Ord BVConst where
  compare (BVConst cx) (BVConst cy) =
    viewPair (\wx x -> viewPair (\wy y ->
      case compareF wx wy of
        LTF -> LT
        EQF | BV.ult x y -> LT
        EQF | BV.ult y x -> GT
        EQF -> EQ
        GTF -> GT
    ) cy) cx

-- | Return the (possibly-cached) name for a literal bitvector value.
litBV ::
  (1 <= w) =>
  WT.NatRepr w ->
  BV.BV w ->
  VerilogM sym n (IExp (WT.BaseBVType w))
litBV w i = do
  cache <- vsBVCache <$> get
  case Map.lookup (BVConst (Pair w i)) cache of
    Just x -> return (Ident (WT.BaseBVRepr w) x)
    Nothing -> do
      x@(Ident _ name) <- mkLet (BVLit w i)
      modify $ \s -> s { vsBVCache = Map.insert (BVConst (Pair w i)) name (vsBVCache s) }
      return x

-- | Return the (possibly-cached) name for a literal Boolean value.
litBool :: Bool -> VerilogM sym n (IExp WT.BaseBoolType)
litBool b = do
  cache <- vsBoolCache <$> get
  case Map.lookup b cache of
    Just x -> return (Ident WT.BaseBoolRepr x)
    Nothing -> do
      x@(Ident _ name) <- mkLet (BoolLit b)
      modify $ \s -> s { vsBoolCache = Map.insert b name (vsBoolCache s) }
      return x

-- | Apply a unary operation to an expression and bind the result to a
-- new, returned name.
unop :: Unop tp -> IExp tp -> VerilogM sym n (IExp tp)
unop op e = mkLet (Unop op e)

-- | Create a conditional, with the given condition, true, and false
-- branches, and bind the result to a new, returned name.
mux ::
  IExp WT.BaseBoolType ->
  IExp tp ->
  IExp tp ->
  VerilogM sym n (IExp tp)
mux e e1 e2 = mkLet (Mux e e1 e2)

-- | Extract a single bit from a bit vector and bind the result to a
-- new, returned name.
bit ::
  IExp (WT.BaseBVType w) ->
  Integer ->
  VerilogM sym n (IExp WT.BaseBoolType)
bit e i = mkLet (Bit e i)

-- | Extract a range of bits from a bit vector and bind the result to a
-- new, returned name. The two `NatRepr` values are the starting index
-- and the number of bits to extract, respectively.
bitSelect ::
  (1 WT.<= len, idx WT.+ len WT.<= w) =>
  IExp (WT.BaseBVType w) ->
  WT.NatRepr idx ->
  WT.NatRepr len ->
  VerilogM sym n (IExp (WT.BaseBVType len))
bitSelect e start len = mkLet (BitSelect e start len)

-- | Concatenate two bit vectors and bind the result to a new, returned
-- name.
concat2 ::
  (w ~ (w1 WT.+ w2), 1 <= w) =>
  WT.NatRepr w ->
  IExp (WT.BaseBVType w1) ->
  IExp (WT.BaseBVType w2) ->
  VerilogM sym n (IExp (WT.BaseBVType w))
concat2 w e1 e2 = mkLet (Concat w [Some e1, Some e2])

-- | A data type for items that may show up in a Verilog module.
data Item where
  Input  :: WT.BaseTypeRepr tp -> Identifier -> Item
  Output :: WT.BaseTypeRepr tp -> Identifier -> Item
  Wire   :: WT.BaseTypeRepr tp -> Identifier -> Item
  Assign :: LHS -> Exp tp -> Item

-- | Necessary monadic operations

data ModuleState sym n =
    ModuleState { vsInputs :: [(Some WT.BaseTypeRepr, Identifier)]
                -- ^ All module inputs, in reverse order.
                , vsOutputs :: [(Some WT.BaseTypeRepr, Bool, Identifier, Some Exp)]
                -- ^ All module outputs, in reverse order. Includes the
                -- type, signedness, name, and initializer of each.
                , vsWires :: [(Some WT.BaseTypeRepr, Bool, Identifier, Some Exp)]
                -- ^ All internal wires, in reverse order. Includes the
                -- type, signedness, name, and initializer of each.
                , vsFreshIdent :: Int
                -- ^ A counter for generating fresh names.
                , vsExpCache :: IdxCache n IExp
                -- ^ An expression cache to preserve sharing present in
                -- the What4 representation.
                , vsBVCache :: Map.Map BVConst Identifier
                -- ^ A cache of bit vector constants, to avoid duplicating constant declarations.
                , vsBoolCache :: Map.Map Bool Identifier
                -- ^ A cache of Boolean constants, to avoid duplicating constant declarations.
                , vsSym :: sym
                -- ^ The What4 symbolic backend to use with `vsBVCache`.
                }

newtype VerilogM sym n a =
 VerilogM (StateT (ModuleState sym n) (ExceptT String IO) a)
 deriving ( Functor
          , Applicative
          , Monad
          , MonadState (ModuleState sym n)
          , MonadError String
          , MonadIO
          )


newtype Module sym n = Module (ModuleState sym n)

-- | Create a Verilog module in the context of a given What4 symbolic
-- backend and a monadic computation that returns an expression name
-- that corresponds to the module's output.
mkModule ::
  sym ->
  [VerilogM sym n (IExp tp)] ->
  ExceptT String IO (Module sym n)
mkModule sym ops = fmap Module $ execVerilogM sym $ do
    es <- sequence ops
    forM_ es $ \e ->
      do out <- freshIdentifier "out"
         addOutput (iexpType e) out (IExp e)

initModuleState :: sym -> IO (ModuleState sym n)
initModuleState sym = do
  cache <- newIdxCache
  return $ ModuleState [] [] [] 0 cache Map.empty Map.empty sym

runVerilogM ::
  VerilogM sym n a ->
  ModuleState sym n ->
  ExceptT String IO (a, ModuleState sym n)
runVerilogM (VerilogM op) = runStateT op

execVerilogM ::
  sym ->
  VerilogM sym n a ->
  ExceptT String IO (ModuleState sym n)
execVerilogM sym op =
  do s <- liftIO $ initModuleState sym
     (_a,m) <- runVerilogM op s
     return m

-- | Returns and records a fresh input with the given type and with a
-- name constructed from the given base.
addFreshInput ::
  WT.BaseTypeRepr tp ->
  Identifier ->
  VerilogM sym n Identifier
addFreshInput tp base = do
  name <- freshIdentifier base
  modify $ \st -> st { vsInputs = (Some tp, name) : vsInputs st }
  return name

-- | Add an output to the current Verilog module state, given a type, a
-- name, and an initializer expression.
addOutput ::
  WT.BaseTypeRepr tp ->
  Identifier ->
  Exp tp ->
  VerilogM sym n ()
addOutput tp name e =
  modify $ \st -> st { vsOutputs = (Some tp, False, name, Some e) : vsOutputs st }

-- | Add a new wire to the current Verilog module state, given a type, a
-- signedness flag, a name, and an initializer expression.
addWire ::
  WT.BaseTypeRepr tp ->
  Bool ->
  Identifier ->
  Exp tp ->
  VerilogM sym n ()
addWire tp isSigned name e =
  modify $ \st -> st { vsWires = (Some tp, isSigned, name, Some e) : vsWires st }

-- | Create a fresh identifier by concatenating the given base with the
-- current fresh identifier counter.
freshIdentifier :: String -> VerilogM sym n Identifier
freshIdentifier basename = do
  st <- get
  let x = vsFreshIdent st
  put $ st { vsFreshIdent = x+1 }
  return $ basename ++ "_" ++ show x


-- | Add a new wire to the current Verilog module state, given a type, a
-- signedness flag, the prefix of a name, and an initializer expression.
-- The name prefix will be freshened by appending current value of the
-- fresh variable counter.
addFreshWire ::
  WT.BaseTypeRepr tp ->
  Bool ->
  String ->
  Exp tp ->
  VerilogM sym n Identifier
addFreshWire repr isSigned basename e = do
  x <- freshIdentifier basename
  addWire repr isSigned x e
  return x

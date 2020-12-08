{-
Module           : What4.Protocol.VerilogWriter.AST
Copyright        : (c) Galois, Inc 2020
Maintainer       : Jennifer Paykin <jpaykin@galois.com>
License          : BSD3

Connecting the Crucible simple builder backend to Verilog that can be read by
ABC.
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

data Unop (tp :: WT.BaseType) where
  Not :: Unop WT.BaseBoolType
  BVNot :: Unop (WT.BaseBVType w)

showUnop :: Unop tp -> String
showUnop Not   = "!"
showUnop BVNot = "~"

showBinop :: Binop inTp outTp -> String
showBinop And      = "&&"
showBinop Or       = "||"
showBinop Xor      = "^^"
showBinop BVAnd    = "&"
showBinop BVOr     = "|"
showBinop BVXor    = "^"
showBinop BVAdd    = "+"
showBinop BVSub    = "-"
showBinop BVMul    = "*"
showBinop BVDiv    = "/"
showBinop BVRem    = "%"
showBinop BVPow    = "**"
showBinop BVShiftL = "<<"
showBinop BVShiftR = ">>"
showBinop BVShiftRA = ">>>"
showBinop Eq       = "=="
showBinop Ne       = "!="
showBinop Lt       = "<"
showBinop Le       = "<="

data IExp (tp :: WT.BaseType) where
  Ident   :: WT.BaseTypeRepr tp -> Identifier -> IExp tp

iexpType :: IExp tp -> WT.BaseTypeRepr tp
iexpType (Ident tp _) = tp

data LHS = LHS Identifier | LHSBit Identifier Integer

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


abcLet :: Exp tp -> VerilogM sym n (IExp tp)
abcLet (IExp x) = return x
abcLet e = do
    let tp = expType e
    x <- addFreshWire tp False "x" e
    return (Ident tp x)

signed :: IExp tp -> VerilogM sym n (IExp tp)
signed e = do
    let tp = iexpType e
    x <- addFreshWire tp True "x" (IExp e)
    return (Ident tp x)

binop ::
  Binop inTp outTp ->
  IExp inTp -> IExp inTp ->
  VerilogM sym n (IExp outTp)
binop op e1 e2 = abcLet (Binop op e1 e2)

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
      x@(Ident _ name) <- abcLet (BVLit w i)
      modify $ \s -> s { vsBVCache = Map.insert (BVConst (Pair w i)) name (vsBVCache s) }
      return x

litBool :: Bool -> VerilogM sym n (IExp WT.BaseBoolType)
litBool b = do
  cache <- vsBoolCache <$> get
  case Map.lookup b cache of
    Just x -> return (Ident WT.BaseBoolRepr x)
    Nothing -> do
      x@(Ident _ name) <- abcLet (BoolLit b)
      modify $ \s -> s { vsBoolCache = Map.insert b name (vsBoolCache s) }
      return x

unop :: Unop tp -> IExp tp -> VerilogM sym n (IExp tp)
unop op e = abcLet (Unop op e)

mux ::
  IExp WT.BaseBoolType ->
  IExp tp ->
  IExp tp ->
  VerilogM sym n (IExp tp)
mux e e1 e2 = abcLet (Mux e e1 e2)

bit ::
  IExp (WT.BaseBVType w) ->
  Integer->
  VerilogM sym n (IExp WT.BaseBoolType)
bit e i = abcLet (Bit e i)

bitSelect ::
  (1 WT.<= len, idx WT.+ len WT.<= w) =>
  IExp (WT.BaseBVType w) ->
  WT.NatRepr idx ->
  WT.NatRepr len ->
  VerilogM sym n (IExp (WT.BaseBVType len))
bitSelect e start len = abcLet (BitSelect e start len)

concat2 ::
  (w ~ (w1 WT.+ w2), 1 <= w) =>
  WT.NatRepr w ->
  IExp (WT.BaseBVType w1) ->
  IExp (WT.BaseBVType w2) ->
  VerilogM sym n (IExp (WT.BaseBVType w))
concat2 w e1 e2 = abcLet (Concat w [Some e1, Some e2])


type Range = (Int,Int)
data Item where
  Input  :: WT.BaseTypeRepr tp -> Identifier -> Item
  Output :: WT.BaseTypeRepr tp -> Identifier -> Item
  Wire   :: WT.BaseTypeRepr tp -> Identifier -> Item
  Assign :: LHS -> Exp tp -> Item

-- | Necessary monadic operations

data ModuleState sym n =
    ModuleState { vsInputs :: [(Some WT.BaseTypeRepr, Identifier)] -- In reverse order
                , vsOutputs :: [(Some WT.BaseTypeRepr, Bool, Identifier, Some Exp)] -- In reverse order
                , vsWires :: [(Some WT.BaseTypeRepr, Bool, Identifier, Some Exp)] -- In reverse order
                , vsFreshIdent :: Int
                , vsExpCache :: IdxCache n IExp
                , vsBVCache :: Map.Map BVConst Identifier
                , vsBoolCache :: Map.Map Bool Identifier
                , vsSym :: sym
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

mkModule ::
  sym ->
  VerilogM sym n (IExp tp) ->
  ExceptT String IO (Module sym n)
mkModule sym op = fmap Module $ execVerilogM sym $ do
    e <- op
    out <- freshIdentifier "out"
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

addFreshInput ::
  WT.BaseTypeRepr tp ->
  Identifier ->
  VerilogM sym n Identifier
addFreshInput tp base = do
  name <- freshIdentifier base
  modify $ \st -> st { vsInputs = (Some tp, name) : vsInputs st }
  return name

addOutput ::
  WT.BaseTypeRepr tp ->
  Identifier ->
  Exp tp ->
  VerilogM sym n ()
addOutput tp name e =
  modify $ \st -> st { vsOutputs = (Some tp, False, name, Some e) : vsOutputs st }

addWire ::
  WT.BaseTypeRepr tp ->
  Bool ->
  Identifier ->
  Exp tp ->
  VerilogM sym n ()
addWire tp isSigned name e =
  modify $ \st -> st { vsWires = (Some tp, isSigned, name, Some e) : vsWires st }

freshIdentifier :: String -> VerilogM sym n Identifier
freshIdentifier basename = do
  st <- get
  let x = vsFreshIdent st
  put $ st { vsFreshIdent = x+1 }
  return $ basename ++ "_" ++ show x

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

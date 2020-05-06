{-|
Module      : What4.Expr.App
Copyright   : (c) Galois Inc, 2015-2016
License     : BSD3
Maintainer  : jhendrix@galois.com

This module defines datastructures that encode the basic
syntax formers used in What4.ExprBuidler.
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module What4.Expr.App where

import           Control.Lens hiding (asIndex, (:>), Empty)
import           Control.Monad
import qualified Data.BitVector.Sized as BV
import           Data.Foldable
import           Data.Hashable
import           Data.Kind
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Maybe
import           Data.Parameterized.Classes
import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.TH.GADT
import           Data.Parameterized.TraversableFC
import           Data.Ratio (numerator, denominator)
import           Data.Text (Text)
import qualified Data.Text as Text
import           Numeric.Natural
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           What4.BaseTypes
import           What4.Interface
import qualified What4.SemiRing as SR
import qualified What4.Expr.ArrayUpdateMap as AUM
import           What4.Expr.BoolMap (BoolMap, Polarity(..), BoolMapView(..), Wrap(..))
import qualified What4.Expr.BoolMap as BM
import           What4.Expr.MATLAB
import           What4.Expr.WeightedSum (WeightedSum, SemiRingProduct)
import qualified What4.Expr.WeightedSum as WSum
import qualified What4.Expr.StringSeq as SSeq
import           What4.Expr.TyFam
import           What4.Expr.UnaryBV (UnaryBV)
import qualified What4.Expr.UnaryBV as UnaryBV

import           What4.Utils.AbstractDomains
import           What4.Utils.Arithmetic
import qualified What4.Utils.BVDomain as BVD
import           What4.Utils.Complex
import           What4.Utils.IncrHash
import qualified What4.Utils.AnnotatedMap as AM


-- | The type of @Nonce@s that should be used with
--   an expression builder with configuration type @t@.
type ExprNonce (t::Type) = Nonce (ExprNonceBrand t)

------------------------------------------------------------------------
-- ExprBoundVar

-- | The Kind of a bound variable.
data VarKind
  = QuantifierVarKind
    -- ^ A variable appearing in a quantifier.
  | LatchVarKind
    -- ^ A variable appearing as a latch input.
  | UninterpVarKind
    -- ^ A variable appearing in a uninterpreted constant

-- | Information about bound variables.
-- Parameter @t@ is a phantom type brand used to track nonces.
--
-- Type @'ExprBoundVar' t@ instantiates the type family
-- @'BoundVar' ('ExprBuilder' t st)@.
--
-- Selector functions are provided to destruct 'ExprBoundVar'
-- values, but the constructor is kept hidden. The preferred way to
-- construct a 'ExprBoundVar' is to use 'freshBoundVar'.
data ExprBoundVar t (tp :: BaseType) =
  BVar { bvarId  :: {-# UNPACK #-} !(ExprNonce t tp)
       , bvarLoc :: !(ExprLoc t)
       , bvarName :: !SolverSymbol
       , bvarType :: !(BaseTypeRepr tp)
       , bvarKind :: !VarKind
       , bvarAbstractValue :: !(Maybe (AbstractValue tp))
       }

instance Eq (ExprBoundVar t tp) where
  x == y = bvarId x == bvarId y

instance TestEquality (ExprBoundVar t) where
  testEquality x y = testEquality (bvarId x) (bvarId y)

instance Ord (ExprBoundVar t tp) where
  compare x y = compare (bvarId x) (bvarId y)

instance OrdF (ExprBoundVar t) where
  compareF x y = compareF (bvarId x) (bvarId y)

instance Hashable (ExprBoundVar t tp) where
  hashWithSalt s x = hashWithSalt s (bvarId x)

instance HashableF (ExprBoundVar t) where
  hashWithSaltF = hashWithSalt

------------------------------------------------------------------------
-- NonceApp

-- | Type @NonceApp t e tp@ encodes the top-level application of an
-- 'Expr'. It includes expression forms that bind variables (contrast
-- with 'App').
--
-- Parameter @t@ is a phantom type brand used to track nonces.
-- Parameter @e@ is used everywhere a recursive sub-expression would
-- go. Uses of the 'NonceApp' type will tie the knot through this
-- parameter. Parameter @tp@ indicates the type of the expression.
data NonceApp t (e :: BaseType -> Type) (tp :: BaseType) where
  Annotation ::
    !(BaseTypeRepr tp) ->
    !(ExprNonce t tp) ->
    !(e tp) ->
    NonceApp t e tp

  Forall :: !(ExprBoundVar t tp)
         -> !(e BaseBoolType)
         -> NonceApp t e BaseBoolType
  Exists :: !(ExprBoundVar t tp)
         -> !(e BaseBoolType)
         -> NonceApp t e BaseBoolType

  -- Create an array from a function
  ArrayFromFn :: !(ExprSymFn t e (idx ::> itp) ret)
              -> NonceApp t e (BaseArrayType (idx ::> itp) ret)

  -- Create an array by mapping over one or more existing arrays.
  MapOverArrays :: !(ExprSymFn t e (ctx::>d) r)
                -> !(Ctx.Assignment BaseTypeRepr (idx ::> itp))
                -> !(Ctx.Assignment (ArrayResultWrapper e (idx ::> itp)) (ctx::>d))
                -> NonceApp t e (BaseArrayType (idx ::> itp) r)

  -- This returns true if all the indices satisfying the given predicate equal true.
  ArrayTrueOnEntries
    :: !(ExprSymFn t e (idx ::> itp) BaseBoolType)
    -> !(e (BaseArrayType (idx ::> itp) BaseBoolType))
    -> NonceApp t e BaseBoolType

  -- Apply a function to some arguments
  FnApp :: !(ExprSymFn t e args ret)
        -> !(Ctx.Assignment e args)
        -> NonceApp t e ret


------------------------------------------------------------------------
-- ExprSymFn

-- | This describes information about an undefined or defined function.
-- Parameter @t@ is a phantom type brand used to track nonces.
data SymFnInfo t e (args :: Ctx BaseType) (ret :: BaseType)
   = UninterpFnInfo !(Ctx.Assignment BaseTypeRepr args)
                    !(BaseTypeRepr ret)
     -- ^ Information about the argument type and return type of an uninterpreted function.

   | DefinedFnInfo !(Ctx.Assignment (ExprBoundVar t) args)
                   !(e ret)
                   !UnfoldPolicy
     -- ^ Information about a defined function.
     -- Includes bound variables and an expression associated to a defined function,
     -- as well as a policy for when to unfold the body.

   | MatlabSolverFnInfo !(MatlabSolverFn e args ret)
                        !(Ctx.Assignment (ExprBoundVar t) args)
                        !(e ret)
     -- ^ This is a function that corresponds to a matlab solver function.
     --   It includes the definition as a ExprBuilder expr to
     --   enable export to other solvers.

-- | This represents a symbolic function in the simulator.
-- Parameter @t@ is a phantom type brand used to track nonces.
--
-- Type @'ExprSymFn' t@ instantiates the type family @'SymFn'
-- ('ExprBuilder' t st)@.
data ExprSymFn t e (args :: Ctx BaseType) (ret :: BaseType)
   = ExprSymFn { symFnId :: !(ExprNonce t (args ::> ret))
                 -- /\ A unique identifier for the function
                 , symFnName :: !SolverSymbol
                 -- /\ Name of the function
                 , symFnInfo :: !(SymFnInfo t e args ret)
                 -- /\ Information about function
                 , symFnLoc  :: !(ExprLoc t)
                 -- /\ Location where function was defined.
                 }

instance Show (ExprSymFn t e args ret) where
  show f | symFnName f == emptySymbol = "f" ++ show (indexValue (symFnId f))
         | otherwise                  = show (symFnName f)


symFnArgTypes :: ExprSymFn t e args ret -> Ctx.Assignment BaseTypeRepr args
symFnArgTypes f =
  case symFnInfo f of
    UninterpFnInfo tps _ -> tps
    DefinedFnInfo vars _ _ -> fmapFC bvarType vars
    MatlabSolverFnInfo fn_id _ _ -> matlabSolverArgTypes fn_id

symFnReturnType :: IsExpr e => ExprSymFn t e args ret -> BaseTypeRepr ret
symFnReturnType f =
  case symFnInfo f of
    UninterpFnInfo _ tp -> tp
    DefinedFnInfo _ r _ -> exprType r
    MatlabSolverFnInfo fn_id _ _ -> matlabSolverReturnType fn_id

-- | Return solver function associated with ExprSymFn if any.
asMatlabSolverFn :: ExprSymFn t e args ret -> Maybe (MatlabSolverFn e args ret)
asMatlabSolverFn f
  | MatlabSolverFnInfo g _ _ <- symFnInfo f = Just g
  | otherwise = Nothing


instance Hashable (ExprSymFn t e args tp) where
  hashWithSalt s f = s `hashWithSalt` symFnId f

testExprSymFnEq ::
  ExprSymFn t e a1 r1 -> ExprSymFn t e a2 r2 -> Maybe ((a1::>r1) :~: (a2::>r2))
testExprSymFnEq f g = testEquality (symFnId f) (symFnId g)


instance IsExpr e => IsSymFn (ExprSymFn t e) where
  fnTestEq x y =
    do Refl <- testEquality (symFnId x) (symFnId y)
       return (Refl, Refl)
  fnArgTypes = symFnArgTypes
  fnReturnType = symFnReturnType



-------------------------------------------------------------------------------
-- BVOrSet

data BVOrNote w = BVOrNote !IncrHash !(BVD.BVDomain w)

instance Semigroup (BVOrNote w) where
  BVOrNote xh xa <> BVOrNote yh ya = BVOrNote (xh <> yh) (BVD.or xa ya)

newtype BVOrSet e w = BVOrSet (AM.AnnotatedMap (Wrap e (BaseBVType w)) (BVOrNote w) ())

traverseBVOrSet :: (HashableF f, HasAbsValue f, OrdF f, Applicative m) =>
  (forall tp. e tp -> m (f tp)) ->
  (BVOrSet e w -> m (BVOrSet f w))
traverseBVOrSet f (BVOrSet m) =
  foldr bvOrInsert (BVOrSet AM.empty) <$> traverse (f . unWrap . fst) (AM.toList m)

bvOrInsert :: (OrdF e, HashableF e, HasAbsValue e) => e (BaseBVType w) -> BVOrSet e w -> BVOrSet e w
bvOrInsert e (BVOrSet m) = BVOrSet $ AM.insert (Wrap e) (BVOrNote (mkIncrHash (hashF e)) (getAbsValue e)) () m

bvOrSingleton :: (OrdF e, HashableF e, HasAbsValue e) => e (BaseBVType w) -> BVOrSet e w
bvOrSingleton e = bvOrInsert e (BVOrSet AM.empty)

bvOrContains :: OrdF e => e (BaseBVType w) -> BVOrSet e w -> Bool
bvOrContains x (BVOrSet m) = isJust $ AM.lookup (Wrap x) m

bvOrUnion :: OrdF e => BVOrSet e w -> BVOrSet e w -> BVOrSet e w
bvOrUnion (BVOrSet x) (BVOrSet y) = BVOrSet (AM.union x y)

bvOrToList :: BVOrSet e w -> [e (BaseBVType w)]
bvOrToList (BVOrSet m) = unWrap . fst <$> AM.toList m

bvOrAbs :: (OrdF e, 1 <= w) => NatRepr w -> BVOrSet e w -> BVD.BVDomain w
bvOrAbs w (BVOrSet m) =
  case AM.annotation m of
    Just (BVOrNote _ a) -> a
    Nothing -> BVD.singleton w 0

instance (OrdF e, TestEquality e) => Eq (BVOrSet e w) where
  BVOrSet x == BVOrSet y = AM.eqBy (\_ _ -> True) x y

instance OrdF e => Hashable (BVOrSet e w) where
  hashWithSalt s (BVOrSet m) =
    case AM.annotation m of
      Just (BVOrNote h _) -> hashWithSalt s h
      Nothing -> s


------------------------------------------------------------------------
-- App

-- | Type @'App' e tp@ encodes the top-level application of an 'Expr'
-- expression. It includes first-order expression forms that do not
-- bind variables (contrast with 'NonceApp').
--
-- Parameter @e@ is used everywhere a recursive sub-expression would
-- go. Uses of the 'App' type will tie the knot through this
-- parameter. Parameter @tp@ indicates the type of the expression.
data App (e :: BaseType -> Type) (tp :: BaseType) where

  ------------------------------------------------------------------------
  -- Generic operations

  BaseIte ::
    !(BaseTypeRepr tp) ->
    !Integer {- Total number of predicates in this ite tree -} ->
    !(e BaseBoolType) ->
    !(e tp) ->
    !(e tp) ->
    App e tp

  BaseEq ::
    !(BaseTypeRepr tp) ->
    !(e tp) ->
    !(e tp) ->
    App e BaseBoolType

  ------------------------------------------------------------------------
  -- Boolean operations

  -- Invariant: The argument to a NotPred must not be another NotPred.
  NotPred :: !(e BaseBoolType) -> App e BaseBoolType

  -- Invariant: The BoolMap must contain at least two elements. No
  -- element may be a NotPred; negated elements must be represented
  -- with Negative element polarity.
  ConjPred :: !(BoolMap e) -> App e BaseBoolType

  ------------------------------------------------------------------------
  -- Semiring operations

  SemiRingSum ::
    {-# UNPACK #-} !(WeightedSum e sr) ->
    App e (SR.SemiRingBase sr)

  -- A product of semiring values
  --
  -- The ExprBuilder should maintain the invariant that none of the values is
  -- a constant, and hence this denotes a non-linear expression.
  -- Multiplications by scalars should use the 'SemiRingSum' constructor.
  SemiRingProd ::
     {-# UNPACK #-} !(SemiRingProduct e sr) ->
     App e (SR.SemiRingBase sr)

  SemiRingLe
     :: !(SR.OrderedSemiRingRepr sr)
     -> !(e (SR.SemiRingBase sr))
     -> !(e (SR.SemiRingBase sr))
     -> App e BaseBoolType

  ------------------------------------------------------------------------
  -- Basic arithmetic operations

  RealIsInteger :: !(e BaseRealType) -> App e BaseBoolType

  -- This does natural number division rounded to zero.
  NatDiv :: !(e BaseNatType)  -> !(e BaseNatType) -> App e BaseNatType
  NatMod :: !(e BaseNatType)  -> !(e BaseNatType) -> App e BaseNatType

  IntDiv :: !(e BaseIntegerType)  -> !(e BaseIntegerType) -> App e BaseIntegerType
  IntMod :: !(e BaseIntegerType)  -> !(e BaseIntegerType) -> App e BaseIntegerType
  IntAbs :: !(e BaseIntegerType)  -> App e BaseIntegerType
  IntDivisible :: !(e BaseIntegerType) -> Natural -> App e BaseBoolType

  RealDiv :: !(e BaseRealType) -> !(e BaseRealType) -> App e BaseRealType

  -- Returns @sqrt(x)@, result is not defined if @x@ is negative.
  RealSqrt :: !(e BaseRealType) -> App e BaseRealType

  ------------------------------------------------------------------------
  -- Operations that introduce irrational numbers.

  Pi :: App e BaseRealType

  RealSin   :: !(e BaseRealType) -> App e BaseRealType
  RealCos   :: !(e BaseRealType) -> App e BaseRealType
  RealATan2 :: !(e BaseRealType) -> !(e BaseRealType) -> App e BaseRealType
  RealSinh  :: !(e BaseRealType) -> App e BaseRealType
  RealCosh  :: !(e BaseRealType) -> App e BaseRealType

  RealExp :: !(e BaseRealType) -> App e BaseRealType
  RealLog :: !(e BaseRealType) -> App e BaseRealType

  --------------------------------
  -- Bitvector operations

  -- Return value of bit at given index.
  BVTestBit :: (1 <= w)
            => !Natural -- Index of bit to test
                        -- (least-significant bit has index 0)
            -> !(e (BaseBVType w))
            -> App e BaseBoolType
  BVSlt :: (1 <= w)
        => !(e (BaseBVType w))
        -> !(e (BaseBVType w))
        -> App e BaseBoolType
  BVUlt :: (1 <= w)
        => !(e (BaseBVType w))
        -> !(e (BaseBVType w))
        -> App e BaseBoolType

  BVOrBits :: (1 <= w) => !(NatRepr w) -> !(BVOrSet e w) -> App e (BaseBVType w)

  -- A unary representation of terms where an integer @i@ is mapped to a
  -- predicate that is true if the unsigned encoding of the value is greater
  -- than or equal to @i@.
  --
  -- The map contains a binding (i -> p_i) when the predicate
  --
  -- As an example, we can encode the value @1@ with the assignment:
  --   { 0 => true ; 2 => false }
  BVUnaryTerm :: (1 <= n)
              => !(UnaryBV (e BaseBoolType) n)
              -> App e (BaseBVType n)

  BVConcat :: (1 <= u, 1 <= v, 1 <= (u+v))
           => !(NatRepr (u+v))
           -> !(e (BaseBVType u))
           -> !(e (BaseBVType v))
           -> App e (BaseBVType (u+v))

  BVSelect :: (1 <= n, idx + n <= w)
              -- First bit to select from (least-significant bit has index 0)
           => !(NatRepr idx)
              -- Number of bits to select, counting up toward more significant bits
           -> !(NatRepr n)
              -- Bitvector to select from.
           -> !(e (BaseBVType w))
           -> App e (BaseBVType n)

  BVFill :: (1 <= w)
         => !(NatRepr w)
         -> !(e BaseBoolType)
         -> App e (BaseBVType w)

  BVUdiv :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)
  BVUrem :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)
  BVSdiv :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)
  BVSrem :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)

  BVShl :: (1 <= w)
        => !(NatRepr w)
        -> !(e (BaseBVType w))
        -> !(e (BaseBVType w))
        -> App e (BaseBVType w)

  BVLshr :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)

  BVAshr :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)

  BVRol :: (1 <= w)
        => !(NatRepr w)
        -> !(e (BaseBVType w)) -- bitvector to rotate
        -> !(e (BaseBVType w)) -- rotate amount
        -> App e (BaseBVType w)

  BVRor :: (1 <= w)
        => !(NatRepr w)
        -> !(e (BaseBVType w))   -- bitvector to rotate
        -> !(e (BaseBVType w))   -- rotate amount
        -> App e (BaseBVType w)

  BVZext :: (1 <= w, w+1 <= r, 1 <= r)
         => !(NatRepr r)
         -> !(e (BaseBVType w))
         -> App e (BaseBVType r)

  BVSext :: (1 <= w, w+1 <= r, 1 <= r)
         => !(NatRepr r)
         -> !(e (BaseBVType w))
         -> App e (BaseBVType r)

  BVPopcount ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(e (BaseBVType w)) ->
    App e (BaseBVType w)

  BVCountTrailingZeros ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(e (BaseBVType w)) ->
    App e (BaseBVType w)

  BVCountLeadingZeros ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(e (BaseBVType w)) ->
    App e (BaseBVType w)

  --------------------------------
  -- Float operations

  FloatPZero :: !(FloatPrecisionRepr fpp) -> App e (BaseFloatType fpp)
  FloatNZero :: !(FloatPrecisionRepr fpp) -> App e (BaseFloatType fpp)
  FloatNaN :: !(FloatPrecisionRepr fpp) -> App e (BaseFloatType fpp)
  FloatPInf :: !(FloatPrecisionRepr fpp) -> App e (BaseFloatType fpp)
  FloatNInf :: !(FloatPrecisionRepr fpp) -> App e (BaseFloatType fpp)
  FloatNeg
    :: !(FloatPrecisionRepr fpp)
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatAbs
    :: !(FloatPrecisionRepr fpp)
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatSqrt
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatAdd
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatSub
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatMul
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatDiv
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatRem
    :: !(FloatPrecisionRepr fpp)
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatMin
    :: !(FloatPrecisionRepr fpp)
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatMax
    :: !(FloatPrecisionRepr fpp)
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatFMA
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatFpEq
    :: !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e BaseBoolType
  FloatFpNe
    :: !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e BaseBoolType
  FloatLe
    :: !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e BaseBoolType
  FloatLt
    :: !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e BaseBoolType
  FloatIsNaN :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatIsInf :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatIsZero :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatIsPos :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatIsNeg :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatIsSubnorm :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatIsNorm :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatCast
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp'))
    -> App e (BaseFloatType fpp)
  FloatRound
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatFromBinary
    :: (2 <= eb, 2 <= sb)
    => !(FloatPrecisionRepr (FloatingPointPrecision eb sb))
    -> !(e (BaseBVType (eb + sb)))
    -> App e (BaseFloatType (FloatingPointPrecision eb sb))
  FloatToBinary
    :: (2 <= eb, 2 <= sb, 1 <= eb + sb)
    => !(FloatPrecisionRepr (FloatingPointPrecision eb sb))
    -> !(e (BaseFloatType (FloatingPointPrecision eb sb)))
    -> App e (BaseBVType (eb + sb))
  BVToFloat
    :: (1 <= w)
    => !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseBVType w))
    -> App e (BaseFloatType fpp)
  SBVToFloat
    :: (1 <= w)
    => !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseBVType w))
    -> App e (BaseFloatType fpp)
  RealToFloat
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e BaseRealType)
    -> App e (BaseFloatType fpp)
  FloatToBV
    :: (1 <= w)
    => !(NatRepr w)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> App e (BaseBVType w)
  FloatToSBV
    :: (1 <= w)
    => !(NatRepr w)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> App e (BaseBVType w)
  FloatToReal :: !(e (BaseFloatType fpp)) -> App e BaseRealType

  ------------------------------------------------------------------------
  -- Array operations

  -- Partial map from concrete indices to array values over another array.
  ArrayMap :: !(Ctx.Assignment BaseTypeRepr (i ::> itp))
           -> !(BaseTypeRepr tp)
                -- /\ The type of the array.
           -> !(AUM.ArrayUpdateMap e (i ::> itp) tp)
              -- /\ Maps indices that are updated to the associated value.
           -> !(e (BaseArrayType (i::> itp) tp))
              -- /\ The underlying array that has been updated.
           -> App e (BaseArrayType (i ::> itp) tp)

  -- Constant array
  ConstantArray :: !(Ctx.Assignment BaseTypeRepr (i ::> tp))
                -> !(BaseTypeRepr b)
                -> !(e b)
                -> App e (BaseArrayType (i::>tp) b)

  UpdateArray :: !(BaseTypeRepr b)
              -> !(Ctx.Assignment BaseTypeRepr (i::>tp))
              -> !(e (BaseArrayType (i::>tp) b))
              -> !(Ctx.Assignment e (i::>tp))
              -> !(e b)
              -> App e (BaseArrayType (i::>tp) b)

  SelectArray :: !(BaseTypeRepr b)
              -> !(e (BaseArrayType (i::>tp) b))
              -> !(Ctx.Assignment e (i::>tp))
              -> App e b

  ------------------------------------------------------------------------
  -- Conversions.

  NatToInteger  :: !(e BaseNatType)  -> App e BaseIntegerType
  -- Converts non-negative integer to nat.
  -- Not defined on negative values.
  IntegerToNat :: !(e BaseIntegerType) -> App e BaseNatType

  IntegerToReal :: !(e BaseIntegerType) -> App e BaseRealType

  -- Convert a real value to an integer
  --
  -- Not defined on non-integral reals.
  RealToInteger :: !(e BaseRealType) -> App e BaseIntegerType

  BVToNat       :: (1 <= w) => !(e (BaseBVType w)) -> App e BaseNatType
  BVToInteger   :: (1 <= w) => !(e (BaseBVType w)) -> App e BaseIntegerType
  SBVToInteger  :: (1 <= w) => !(e (BaseBVType w)) -> App e BaseIntegerType

  -- Converts integer to a bitvector.  The number is interpreted modulo 2^n.
  IntegerToBV  :: (1 <= w) => !(e BaseIntegerType) -> NatRepr w -> App e (BaseBVType w)

  RoundReal :: !(e BaseRealType) -> App e BaseIntegerType
  RoundEvenReal :: !(e BaseRealType) -> App e BaseIntegerType
  FloorReal :: !(e BaseRealType) -> App e BaseIntegerType
  CeilReal  :: !(e BaseRealType) -> App e BaseIntegerType

  ------------------------------------------------------------------------
  -- Complex operations

  Cplx  :: {-# UNPACK #-} !(Complex (e BaseRealType)) -> App e BaseComplexType
  RealPart :: !(e BaseComplexType) -> App e BaseRealType
  ImagPart :: !(e BaseComplexType) -> App e BaseRealType

  ------------------------------------------------------------------------
  -- Strings

  StringContains :: !(e (BaseStringType si))
                 -> !(e (BaseStringType si))
                 -> App e BaseBoolType

  StringIsPrefixOf :: !(e (BaseStringType si))
                 -> !(e (BaseStringType si))
                 -> App e BaseBoolType

  StringIsSuffixOf :: !(e (BaseStringType si))
                 -> !(e (BaseStringType si))
                 -> App e BaseBoolType

  StringIndexOf :: !(e (BaseStringType si))
                -> !(e (BaseStringType si))
                -> !(e BaseNatType)
                -> App e BaseIntegerType

  StringSubstring :: !(StringInfoRepr si)
                  -> !(e (BaseStringType si))
                  -> !(e BaseNatType)
                  -> !(e BaseNatType)
                  -> App e (BaseStringType si)

  StringAppend :: !(StringInfoRepr si)
               -> !(SSeq.StringSeq e si)
               -> App e (BaseStringType si)

  StringLength :: !(e (BaseStringType si))
               -> App e BaseNatType

  ------------------------------------------------------------------------
  -- Structs

  -- A struct with its fields.
  StructCtor :: !(Ctx.Assignment BaseTypeRepr flds)
             -> !(Ctx.Assignment e flds)
             -> App e (BaseStructType flds)

  StructField :: !(e (BaseStructType flds))
              -> !(Ctx.Index flds tp)
              -> !(BaseTypeRepr tp)
              -> App e tp

------------------------------------------------------------------------
-- Types

nonceAppType :: IsExpr e => NonceApp t e tp -> BaseTypeRepr tp
nonceAppType a =
  case a of
    Annotation tpr _ _ -> tpr
    Forall{} -> knownRepr
    Exists{} -> knownRepr
    ArrayFromFn   fn       -> BaseArrayRepr (symFnArgTypes fn) (symFnReturnType fn)
    MapOverArrays fn idx _ -> BaseArrayRepr idx (symFnReturnType fn)
    ArrayTrueOnEntries _ _ -> knownRepr
    FnApp f _ ->  symFnReturnType f

appType :: App e tp -> BaseTypeRepr tp
appType a =
  case a of
    BaseIte tp _ _ _ _ -> tp
    BaseEq{} -> knownRepr

    NotPred{} -> knownRepr
    ConjPred{} -> knownRepr

    RealIsInteger{} -> knownRepr
    BVTestBit{} -> knownRepr
    BVSlt{}   -> knownRepr
    BVUlt{}   -> knownRepr

    NatDiv{} -> knownRepr
    NatMod{} -> knownRepr

    IntDiv{} -> knownRepr
    IntMod{} -> knownRepr
    IntAbs{} -> knownRepr
    IntDivisible{} -> knownRepr

    SemiRingLe{} -> knownRepr
    SemiRingProd pd -> SR.semiRingBase (WSum.prodRepr pd)
    SemiRingSum s -> SR.semiRingBase (WSum.sumRepr s)

    RealDiv{} -> knownRepr
    RealSqrt{} -> knownRepr

    RoundReal{} -> knownRepr
    RoundEvenReal{} -> knownRepr
    FloorReal{} -> knownRepr
    CeilReal{}  -> knownRepr

    Pi -> knownRepr
    RealSin{}   -> knownRepr
    RealCos{}   -> knownRepr
    RealATan2{} -> knownRepr
    RealSinh{}  -> knownRepr
    RealCosh{}  -> knownRepr

    RealExp{} -> knownRepr
    RealLog{} -> knownRepr

    BVUnaryTerm u  -> BaseBVRepr (UnaryBV.width u)
    BVOrBits w _ -> BaseBVRepr w
    BVConcat w _ _ -> BaseBVRepr w
    BVSelect _ n _ -> BaseBVRepr n
    BVUdiv w _ _ -> BaseBVRepr w
    BVUrem w _ _ -> BaseBVRepr w
    BVSdiv w _ _ -> BaseBVRepr w
    BVSrem w _ _ -> BaseBVRepr w
    BVShl  w _ _  -> BaseBVRepr w
    BVLshr w _ _ -> BaseBVRepr w
    BVAshr w _ _ -> BaseBVRepr w
    BVRol w _ _ -> BaseBVRepr w
    BVRor w _ _ -> BaseBVRepr w
    BVPopcount w _ -> BaseBVRepr w
    BVCountLeadingZeros w _ -> BaseBVRepr w
    BVCountTrailingZeros w _ -> BaseBVRepr w
    BVZext  w _ -> BaseBVRepr w
    BVSext  w _ -> BaseBVRepr w
    BVFill w _ -> BaseBVRepr w

    FloatPZero fpp -> BaseFloatRepr fpp
    FloatNZero fpp -> BaseFloatRepr fpp
    FloatNaN fpp -> BaseFloatRepr fpp
    FloatPInf fpp -> BaseFloatRepr fpp
    FloatNInf fpp -> BaseFloatRepr fpp
    FloatNeg fpp _ -> BaseFloatRepr fpp
    FloatAbs fpp _ -> BaseFloatRepr fpp
    FloatSqrt fpp _ _ -> BaseFloatRepr fpp
    FloatAdd fpp _ _ _ -> BaseFloatRepr fpp
    FloatSub fpp _ _ _ -> BaseFloatRepr fpp
    FloatMul fpp _ _ _ -> BaseFloatRepr fpp
    FloatDiv fpp _ _ _ -> BaseFloatRepr fpp
    FloatRem fpp _ _ -> BaseFloatRepr fpp
    FloatMin fpp _ _ -> BaseFloatRepr fpp
    FloatMax fpp _ _ -> BaseFloatRepr fpp
    FloatFMA fpp _ _ _ _ -> BaseFloatRepr fpp
    FloatFpEq{} -> knownRepr
    FloatFpNe{} -> knownRepr
    FloatLe{} -> knownRepr
    FloatLt{} -> knownRepr
    FloatIsNaN{} -> knownRepr
    FloatIsInf{} -> knownRepr
    FloatIsZero{} -> knownRepr
    FloatIsPos{} -> knownRepr
    FloatIsNeg{} -> knownRepr
    FloatIsSubnorm{} -> knownRepr
    FloatIsNorm{} -> knownRepr
    FloatCast fpp _ _ -> BaseFloatRepr fpp
    FloatRound fpp _ _ -> BaseFloatRepr fpp
    FloatFromBinary fpp _ -> BaseFloatRepr fpp
    FloatToBinary fpp _ -> floatPrecisionToBVType fpp
    BVToFloat fpp _ _ -> BaseFloatRepr fpp
    SBVToFloat fpp _ _ -> BaseFloatRepr fpp
    RealToFloat fpp _ _ -> BaseFloatRepr fpp
    FloatToBV w _ _ -> BaseBVRepr w
    FloatToSBV w _ _ -> BaseBVRepr w
    FloatToReal{} -> knownRepr

    ArrayMap      idx b _ _ -> BaseArrayRepr idx b
    ConstantArray idx b _   -> BaseArrayRepr idx b
    SelectArray b _ _       -> b
    UpdateArray b itp _ _ _     -> BaseArrayRepr itp b

    NatToInteger{} -> knownRepr
    IntegerToReal{} -> knownRepr
    BVToNat{} -> knownRepr
    BVToInteger{} -> knownRepr
    SBVToInteger{} -> knownRepr

    IntegerToNat{} -> knownRepr
    IntegerToBV _ w -> BaseBVRepr w

    RealToInteger{} -> knownRepr

    Cplx{} -> knownRepr
    RealPart{} -> knownRepr
    ImagPart{} -> knownRepr

    StringContains{} -> knownRepr
    StringIsPrefixOf{} -> knownRepr
    StringIsSuffixOf{} -> knownRepr
    StringIndexOf{} -> knownRepr
    StringSubstring si _ _ _ -> BaseStringRepr si
    StringAppend si _ -> BaseStringRepr si
    StringLength{} -> knownRepr

    StructCtor flds _     -> BaseStructRepr flds
    StructField _ _ tp    -> tp


------------------------------------------------------------------------
-- abstractEval

-- | Return an unconstrained abstract value.
unconstrainedAbsValue :: BaseTypeRepr tp -> AbstractValue tp
unconstrainedAbsValue tp = withAbstractable tp (avTop tp)


-- | Return abstract domain associated with a nonce app
quantAbsEval :: IsExpr e =>
  (forall u . e u -> AbstractValue u) ->
  NonceApp t e tp ->
  AbstractValue tp
quantAbsEval f q =
  case q of
    Annotation _ _ v -> f v
    Forall _ v -> f v
    Exists _ v -> f v
    ArrayFromFn _       -> unconstrainedAbsValue (nonceAppType q)
    MapOverArrays g _ _ -> unconstrainedAbsValue tp
      where tp = symFnReturnType g
    ArrayTrueOnEntries _ a -> f a
    FnApp g _           -> unconstrainedAbsValue (symFnReturnType g)

abstractEval :: (IsExpr e, HashableF e, OrdF e) =>
  (forall u . e u -> AbstractValue u) ->
  App e tp ->
  AbstractValue tp
abstractEval f a0 = do
  case a0 of

    BaseIte tp _ _c x y -> withAbstractable tp $ avJoin tp (f x) (f y)
    BaseEq{} -> Nothing

    NotPred{} -> Nothing
    ConjPred{} -> Nothing

    SemiRingLe{} -> Nothing
    RealIsInteger{} -> Nothing
    BVTestBit{} -> Nothing
    BVSlt{} -> Nothing
    BVUlt{} -> Nothing

    ------------------------------------------------------------------------
    -- Arithmetic operations

    NatDiv x y -> natRangeDiv (f x) (f y)
    NatMod x y -> natRangeMod (f x) (f y)

    IntAbs x -> intAbsRange (f x)
    IntDiv x y -> intDivRange (f x) (f y)
    IntMod x y -> intModRange (f x) (f y)

    IntDivisible{} -> Nothing

    SemiRingSum s -> WSum.sumAbsValue s
    SemiRingProd pd -> WSum.prodAbsValue pd

    BVOrBits w m -> bvOrAbs w m

    RealDiv _ _ -> ravUnbounded
    RealSqrt _  -> ravUnbounded
    Pi -> ravConcreteRange 3.14 3.15
    RealSin _ -> ravConcreteRange (-1) 1
    RealCos _ -> ravConcreteRange (-1) 1
    RealATan2 _ _ -> ravUnbounded
    RealSinh _ -> ravUnbounded
    RealCosh _ -> ravUnbounded
    RealExp _ -> ravUnbounded
    RealLog _ -> ravUnbounded

    BVUnaryTerm u -> UnaryBV.domain asConstantPred u
    BVConcat _ x y -> BVD.concat (bvWidth x) (f x) (bvWidth y) (f y)

    BVSelect i n x -> BVD.select i n (f x)
    BVUdiv _ x y -> BVD.udiv (f x) (f y)
    BVUrem _ x y -> BVD.urem (f x) (f y)
    BVSdiv w x y -> BVD.sdiv w (f x) (f y)
    BVSrem w x y -> BVD.srem w (f x) (f y)

    BVShl  w x y -> BVD.shl w (f x) (f y)
    BVLshr w x y -> BVD.lshr w (f x) (f y)
    BVAshr w x y -> BVD.ashr w (f x) (f y)
    BVRol  w x y -> BVD.rol w  (f x) (f y)
    BVRor  w x y -> BVD.ror w  (f x) (f y)
    BVZext w x   -> BVD.zext (f x) w
    BVSext w x   -> BVD.sext (bvWidth x) (f x) w
    BVFill w _   -> BVD.range w (-1) 0

    BVPopcount w x -> BVD.popcnt w (f x)
    BVCountLeadingZeros w x -> BVD.clz w (f x)
    BVCountTrailingZeros w x -> BVD.ctz w (f x)

    FloatPZero{} -> ()
    FloatNZero{} -> ()
    FloatNaN{} -> ()
    FloatPInf{} -> ()
    FloatNInf{} -> ()
    FloatNeg{} -> ()
    FloatAbs{} -> ()
    FloatSqrt{} -> ()
    FloatAdd{} -> ()
    FloatSub{} -> ()
    FloatMul{} -> ()
    FloatDiv{} -> ()
    FloatRem{} -> ()
    FloatMin{} -> ()
    FloatMax{} -> ()
    FloatFMA{} -> ()
    FloatFpEq{} -> Nothing
    FloatFpNe{} -> Nothing
    FloatLe{} -> Nothing
    FloatLt{} -> Nothing
    FloatIsNaN{} -> Nothing
    FloatIsInf{} -> Nothing
    FloatIsZero{} -> Nothing
    FloatIsPos{} -> Nothing
    FloatIsNeg{} -> Nothing
    FloatIsSubnorm{} -> Nothing
    FloatIsNorm{} -> Nothing
    FloatCast{} -> ()
    FloatRound{} -> ()
    FloatFromBinary{} -> ()
    FloatToBinary fpp _ -> case floatPrecisionToBVType fpp of
      BaseBVRepr w -> BVD.any w
    BVToFloat{} -> ()
    SBVToFloat{} -> ()
    RealToFloat{} -> ()
    FloatToBV w _ _ -> BVD.any w
    FloatToSBV w _ _ -> BVD.any w
    FloatToReal{} -> ravUnbounded

    ArrayMap _ bRepr m d ->
      withAbstractable bRepr $
      case AUM.arrayUpdateAbs m of
        Nothing -> f d
        Just a -> avJoin bRepr (f d) a
    ConstantArray _idxRepr _bRepr v -> f v

    SelectArray _bRepr a _i -> f a  -- FIXME?
    UpdateArray bRepr _ a _i v -> withAbstractable bRepr $ avJoin bRepr (f a) (f v)

    NatToInteger x -> natRangeToRange (f x)
    IntegerToReal x -> RAV (mapRange toRational (f x)) (Just True)
    BVToNat x -> natRange (fromInteger lx) (Inclusive (fromInteger ux))
      where (lx, ux) = BVD.ubounds (f x)
    BVToInteger x -> valueRange (Inclusive lx) (Inclusive ux)
      where (lx, ux) = BVD.ubounds (f x)
    SBVToInteger x -> valueRange (Inclusive lx) (Inclusive ux)
      where (lx, ux) = BVD.sbounds (bvWidth x) (f x)
    RoundReal x -> mapRange roundAway (ravRange (f x))
    RoundEvenReal x -> mapRange round (ravRange (f x))
    FloorReal x -> mapRange floor (ravRange (f x))
    CeilReal x  -> mapRange ceiling (ravRange (f x))
    IntegerToNat x -> intRangeToNatRange (f x)
    IntegerToBV x w -> BVD.range w l u
      where rng = f x
            l = case rangeLowBound rng of
                  Unbounded -> minUnsigned w
                  Inclusive v -> max (minUnsigned w) v
            u = case rangeHiBound rng of
                  Unbounded -> maxUnsigned w
                  Inclusive v -> min (maxUnsigned w) v
    RealToInteger x -> valueRange (ceiling <$> lx) (floor <$> ux)
      where lx = rangeLowBound rng
            ux = rangeHiBound rng
            rng = ravRange (f x)

    Cplx c -> f <$> c
    RealPart x -> realPart (f x)
    ImagPart x -> imagPart (f x)

    StringContains{} -> Nothing
    StringIsPrefixOf{} -> Nothing
    StringIsSuffixOf{} -> Nothing
    StringLength s -> stringAbsLength (f s)
    StringSubstring _ s t l -> stringAbsSubstring (f s) (f t) (f l)
    StringIndexOf s t k -> stringAbsIndexOf (f s) (f t) (f k)
    StringAppend _ xs -> SSeq.stringSeqAbs xs

    StructCtor _ flds -> fmapFC (\v -> AbstractValueWrapper (f v)) flds
    StructField s idx _ -> unwrapAV (f s Ctx.! idx)


reduceApp :: IsExprBuilder sym
          => sym
          -> (forall w. (1 <= w) => sym -> UnaryBV (Pred sym) w -> IO (SymExpr sym (BaseBVType w)))
          -> App (SymExpr sym) tp
          -> IO (SymExpr sym tp)
reduceApp sym unary a0 = do
  case a0 of
    BaseIte _ _ c x y -> baseTypeIte sym c x y
    BaseEq _ x y -> isEq sym x y

    NotPred x -> notPred sym x
    ConjPred bm ->
      case BM.viewBoolMap bm of
        BoolMapDualUnit -> return $ falsePred sym
        BoolMapUnit     -> return $ truePred sym
        BoolMapTerms tms ->
          do let pol (p, Positive) = return p
                 pol (p, Negative) = notPred sym p
             x:|xs <- mapM pol tms
             foldM (andPred sym) x xs

    SemiRingSum s ->
      case WSum.sumRepr s of
        SR.SemiRingNatRepr ->
          WSum.evalM (natAdd sym) (\c x -> natMul sym x =<< natLit sym c) (natLit sym) s
        SR.SemiRingIntegerRepr ->
          WSum.evalM (intAdd sym) (\c x -> intMul sym x =<< intLit sym c) (intLit sym) s
        SR.SemiRingRealRepr ->
          WSum.evalM (realAdd sym) (\c x -> realMul sym x =<< realLit sym c) (realLit sym) s
        SR.SemiRingBVRepr SR.BVArithRepr w ->
          WSum.evalM (bvAdd sym) (\c x -> bvMul sym x =<< bvLit sym w c) (bvLit sym w) s
        SR.SemiRingBVRepr SR.BVBitsRepr w ->
          WSum.evalM (bvXorBits sym) (\c x -> bvAndBits sym x =<< bvLit sym w c) (bvLit sym w) s

    SemiRingProd pd ->
      case WSum.prodRepr pd of
        SR.SemiRingNatRepr ->
          maybe (natLit sym 1) return =<< WSum.prodEvalM (natMul sym) return pd
        SR.SemiRingIntegerRepr ->
          maybe (intLit sym 1) return =<< WSum.prodEvalM (intMul sym) return pd
        SR.SemiRingRealRepr ->
          maybe (realLit sym 1) return =<< WSum.prodEvalM (realMul sym) return pd
        SR.SemiRingBVRepr SR.BVArithRepr w ->
          maybe (bvLit sym w (BV.one w)) return =<< WSum.prodEvalM (bvMul sym) return pd
        SR.SemiRingBVRepr SR.BVBitsRepr w ->
          maybe (bvLit sym w (BV.maxUnsigned w)) return =<< WSum.prodEvalM (bvAndBits sym) return pd

    SemiRingLe SR.OrderedSemiRingRealRepr x y -> realLe sym x y
    SemiRingLe SR.OrderedSemiRingIntegerRepr x y -> intLe sym x y
    SemiRingLe SR.OrderedSemiRingNatRepr x y -> natLe sym x y

    RealIsInteger x -> isInteger sym x

    NatDiv x y -> natDiv sym x y
    NatMod x y -> natMod sym x y

    IntDiv x y -> intDiv sym x y
    IntMod x y -> intMod sym x y
    IntAbs x -> intAbs sym x
    IntDivisible x k -> intDivisible sym x k

    RealDiv x y -> realDiv sym x y
    RealSqrt x  -> realSqrt sym x

    Pi -> realPi sym
    RealSin x -> realSin sym x
    RealCos x -> realCos sym x
    RealATan2 y x -> realAtan2 sym y x
    RealSinh x -> realSinh sym x
    RealCosh x -> realCosh sym x
    RealExp x -> realExp sym x
    RealLog x -> realLog sym x

    BVOrBits w bs ->
      case bvOrToList bs of
        [] -> bvLit sym w (BV.zero w)
        (x:xs) -> foldM (bvOrBits sym) x xs

    BVTestBit i e -> testBitBV sym i e
    BVSlt x y -> bvSlt sym x y
    BVUlt x y -> bvUlt sym x y
    BVUnaryTerm x -> unary sym x
    BVConcat _ x y -> bvConcat sym x y
    BVSelect idx n x -> bvSelect sym idx n x
    BVUdiv _ x y -> bvUdiv sym x y
    BVUrem _ x y -> bvUrem sym x y
    BVSdiv _ x y -> bvSdiv sym x y
    BVSrem _ x y -> bvSrem sym x y
    BVShl _ x y  -> bvShl  sym x y
    BVLshr _ x y -> bvLshr sym x y
    BVAshr _ x y -> bvAshr sym x y
    BVRol  _ x y -> bvRol sym x y
    BVRor  _ x y -> bvRor sym x y
    BVZext  w x  -> bvZext sym w x
    BVSext  w x  -> bvSext sym w x
    BVPopcount _ x -> bvPopcount sym x
    BVFill w p -> bvFill sym w p
    BVCountLeadingZeros _ x -> bvCountLeadingZeros sym x
    BVCountTrailingZeros _ x -> bvCountTrailingZeros sym x

    FloatPZero fpp -> floatPZero sym fpp
    FloatNZero fpp -> floatNZero sym fpp
    FloatNaN   fpp -> floatNaN sym fpp
    FloatPInf  fpp -> floatPInf sym fpp
    FloatNInf  fpp -> floatNInf sym fpp
    FloatNeg _ x -> floatNeg sym x
    FloatAbs _ x -> floatAbs sym x
    FloatSqrt _ r x -> floatSqrt sym r x
    FloatAdd _ r x y -> floatAdd sym r x y
    FloatSub _ r x y -> floatSub sym r x y
    FloatMul _ r x y -> floatMul sym r x y
    FloatDiv _ r x y -> floatDiv sym r x y
    FloatRem _ x y -> floatRem sym x y
    FloatMin _ x y -> floatMin sym x y
    FloatMax _ x y -> floatMax sym x y
    FloatFMA _ r x y z -> floatFMA sym r x y z
    FloatFpEq x y -> floatFpEq sym x y
    FloatFpNe x y -> floatFpNe sym x y
    FloatLe   x y -> floatLe sym x y
    FloatLt   x y -> floatLt sym x y
    FloatIsNaN     x -> floatIsNaN sym x
    FloatIsInf     x -> floatIsInf sym x
    FloatIsZero    x -> floatIsZero sym x
    FloatIsPos     x -> floatIsPos sym x
    FloatIsNeg     x -> floatIsNeg sym x
    FloatIsSubnorm x -> floatIsSubnorm sym x
    FloatIsNorm    x -> floatIsNorm sym x
    FloatCast fpp r x -> floatCast sym fpp r x
    FloatRound  _ r x -> floatRound sym r x
    FloatFromBinary fpp x -> floatFromBinary sym fpp x
    FloatToBinary   _   x -> floatToBinary sym x
    BVToFloat   fpp r x -> bvToFloat sym fpp r x
    SBVToFloat  fpp r x -> sbvToFloat sym fpp r x
    RealToFloat fpp r x -> realToFloat sym fpp r x
    FloatToBV   w   r x -> floatToBV sym w r x
    FloatToSBV  w   r x -> floatToSBV sym w r x
    FloatToReal x -> floatToReal sym x

    ArrayMap _ _ m def_map ->
      arrayUpdateAtIdxLits sym m def_map
    ConstantArray idx_tp _ e -> constantArray sym idx_tp e
    SelectArray _ a i     -> arrayLookup sym a i
    UpdateArray _ _ a i v -> arrayUpdate sym a i v

    NatToInteger x -> natToInteger sym x
    IntegerToNat x -> integerToNat sym x
    IntegerToReal x -> integerToReal sym x
    RealToInteger x -> realToInteger sym x

    BVToNat x       -> bvToNat sym x
    BVToInteger x   -> bvToInteger sym x
    SBVToInteger x  -> sbvToInteger sym x
    IntegerToBV x w -> integerToBV sym x w

    RoundReal x -> realRound sym x
    RoundEvenReal x -> realRoundEven sym x
    FloorReal x -> realFloor sym x
    CeilReal  x -> realCeil sym x

    Cplx c     -> mkComplex sym c
    RealPart x -> getRealPart sym x
    ImagPart x -> getImagPart sym x

    StringIndexOf x y k -> stringIndexOf sym x y k
    StringContains x y -> stringContains sym x y
    StringIsPrefixOf x y -> stringIsPrefixOf sym x y
    StringIsSuffixOf x y -> stringIsSuffixOf sym x y
    StringSubstring _ x off len -> stringSubstring sym x off len

    StringAppend si xs ->
       do e <- stringEmpty sym si
          let f x (SSeq.StringSeqLiteral l) = stringConcat sym x =<< stringLit sym l
              f x (SSeq.StringSeqTerm y) = stringConcat sym x y
          foldM f e (SSeq.toList xs)

    StringLength x -> stringLength sym x

    StructCtor _ args -> mkStruct sym args
    StructField s i _ -> structField sym s i



-- Dummy declaration splice to bring App into template haskell scope.
$(return [])

------------------------------------------------------------------------
-- App operations

ppBoundVar :: forall t tp. ExprBoundVar t tp -> String
ppBoundVar v =
  case bvarKind v of
    QuantifierVarKind -> ppVar "?" (bvarName v) (bvarId v) (bvarType v)
    LatchVarKind   -> ppVar "l" (bvarName v) (bvarId v) (bvarType v)
    UninterpVarKind -> ppVar "c" (bvarName v) (bvarId v) (bvarType v)

  where
  ppVar pr sym i tp = pr ++ show sym ++ "@" ++ show (indexValue i) ++ ":" ++ ppVarTypeCode tp


instance Show (ExprBoundVar t tp) where
  show = ppBoundVar

instance ShowF (ExprBoundVar t)


-- | Pretty print a code to identify the type of constant.
ppVarTypeCode :: BaseTypeRepr tp -> String
ppVarTypeCode tp =
  case tp of
    BaseNatRepr     -> "n"
    BaseBoolRepr    -> "b"
    BaseBVRepr _    -> "bv"
    BaseIntegerRepr -> "i"
    BaseRealRepr    -> "r"
    BaseFloatRepr _ -> "f"
    BaseStringRepr _ -> "s"
    BaseComplexRepr -> "c"
    BaseArrayRepr _ _ -> "a"
    BaseStructRepr _ -> "struct"

-- | Either a argument or text or text
data PrettyArg (e :: BaseType -> Type) where
  PrettyArg  :: e tp -> PrettyArg e
  PrettyText :: Text -> PrettyArg e
  PrettyFunc :: Text -> [PrettyArg e] -> PrettyArg e

exprPrettyArg :: e tp -> PrettyArg e
exprPrettyArg e = PrettyArg e

exprPrettyIndices :: Ctx.Assignment e ctx -> [PrettyArg e]
exprPrettyIndices = toListFC exprPrettyArg

stringPrettyArg :: String -> PrettyArg e
stringPrettyArg x = PrettyText $! Text.pack x

showPrettyArg :: Show a => a -> PrettyArg e
showPrettyArg x = stringPrettyArg $! show x

type PrettyApp e = (Text, [PrettyArg e])

prettyApp :: Text -> [PrettyArg e] -> PrettyApp e
prettyApp nm args = (nm, args)

ppNonceApp :: forall m t e tp
           . Applicative m
           => (forall ctx r . ExprSymFn t e ctx r -> m (PrettyArg e))
           -> NonceApp t e tp
           -> m (PrettyApp e)
ppNonceApp ppFn a0 = do
  case a0 of
    Annotation _ n x -> pure $ prettyApp "annotation" [ showPrettyArg n, exprPrettyArg x ]
    Forall v x -> pure $ prettyApp "forall" [ stringPrettyArg (ppBoundVar v), exprPrettyArg x ]
    Exists v x -> pure $ prettyApp "exists" [ stringPrettyArg (ppBoundVar v), exprPrettyArg x ]
    ArrayFromFn f -> resolve <$> ppFn f
      where resolve f_nm = prettyApp "arrayFromFn" [ f_nm ]
    MapOverArrays f _ args -> resolve <$> ppFn f
      where resolve f_nm = prettyApp "mapArray" (f_nm : arg_nms)
            arg_nms = toListFC (\(ArrayResultWrapper a) -> exprPrettyArg a) args
    ArrayTrueOnEntries f a -> resolve <$> ppFn f
      where resolve f_nm = prettyApp "arrayTrueOnEntries" [ f_nm, a_nm ]
            a_nm = exprPrettyArg a
    FnApp f a -> resolve <$> ppFn f
      where resolve f_nm = prettyApp "apply" (f_nm : toListFC exprPrettyArg a)

instance ShowF e => Pretty (App e u) where
  pretty a = text (Text.unpack nm) <+> sep (ppArg <$> args)
    where (nm, args) = ppApp' a
          ppArg :: PrettyArg e -> Doc
          ppArg (PrettyArg e) = text (showF e)
          ppArg (PrettyText txt) = text (Text.unpack txt)
          ppArg (PrettyFunc fnm fargs) = parens (text (Text.unpack fnm) <+> sep (ppArg <$> fargs))

instance ShowF e => Show (App e u) where
  show = show . pretty

ppApp' :: forall e u . App e u -> PrettyApp e
ppApp' a0 = do
  let ppSExpr :: Text -> [e x] -> PrettyApp e
      ppSExpr f l = prettyApp f (exprPrettyArg <$> l)

  case a0 of
    BaseIte _ _ c x y -> prettyApp "ite" [exprPrettyArg c, exprPrettyArg x, exprPrettyArg y]
    BaseEq _ x y -> ppSExpr "eq" [x, y]

    NotPred x -> ppSExpr "not" [x]

    ConjPred xs ->
      let pol (x,Positive) = exprPrettyArg x
          pol (x,Negative) = PrettyFunc "not" [ exprPrettyArg x ]
       in
       case BM.viewBoolMap xs of
         BoolMapUnit      -> prettyApp "true" []
         BoolMapDualUnit  -> prettyApp "false" []
         BoolMapTerms tms -> prettyApp "and" (map pol (toList tms))

    RealIsInteger x -> ppSExpr "isInteger" [x]
    BVTestBit i x   -> prettyApp "testBit"  [exprPrettyArg x, showPrettyArg i]
    BVUlt x y -> ppSExpr "bvUlt" [x, y]
    BVSlt x y -> ppSExpr "bvSlt" [x, y]

    NatDiv x y -> ppSExpr "natDiv" [x, y]
    NatMod x y -> ppSExpr "natMod" [x, y]

    IntAbs x   -> prettyApp "intAbs" [exprPrettyArg x]
    IntDiv x y -> prettyApp "intDiv" [exprPrettyArg x, exprPrettyArg y]
    IntMod x y -> prettyApp "intMod" [exprPrettyArg x, exprPrettyArg y]
    IntDivisible x k -> prettyApp "intDivisible" [exprPrettyArg x, showPrettyArg k]

    SemiRingLe sr x y ->
      case sr of
        SR.OrderedSemiRingRealRepr    -> ppSExpr "realLe" [x, y]
        SR.OrderedSemiRingIntegerRepr -> ppSExpr "intLe" [x, y]
        SR.OrderedSemiRingNatRepr     -> ppSExpr "natLe" [x, y]

    SemiRingSum s ->
      case WSum.sumRepr s of
        SR.SemiRingRealRepr -> prettyApp "realSum" (WSum.eval (++) ppEntry ppConstant s)
          where ppConstant 0 = []
                ppConstant c = [ stringPrettyArg (ppRat c) ]
                ppEntry 1 e  = [ exprPrettyArg e ]
                ppEntry sm e = [ PrettyFunc "realAdd" [stringPrettyArg (ppRat sm), exprPrettyArg e ] ]
                ppRat r | d == 1 = show n
                        | otherwise = "(" ++ show n ++ "/" ++ show d ++ ")"
                     where n = numerator r
                           d = denominator r

        SR.SemiRingIntegerRepr -> prettyApp "intSum" (WSum.eval (++) ppEntry ppConstant s)
          where ppConstant 0 = []
                ppConstant c = [ stringPrettyArg (show c) ]
                ppEntry 1 e  = [ exprPrettyArg e ]
                ppEntry sm e = [ PrettyFunc "intMul" [stringPrettyArg (show sm), exprPrettyArg e ] ]

        SR.SemiRingNatRepr -> prettyApp "natSum" (WSum.eval (++) ppEntry ppConstant s)
          where ppConstant 0 = []
                ppConstant c = [ stringPrettyArg (show c) ]
                ppEntry 1 e  = [ exprPrettyArg e ]
                ppEntry sm e = [ PrettyFunc "natMul" [stringPrettyArg (show sm), exprPrettyArg e ] ]

        SR.SemiRingBVRepr SR.BVArithRepr w -> prettyApp "bvSum" (WSum.eval (++) ppEntry ppConstant s)
          where ppConstant (BV.BV 0) = []
                ppConstant c = [ stringPrettyArg (ppBV c) ]
                ppEntry sm e
                  | sm == BV.one w = [ exprPrettyArg e ]
                  | otherwise = [ PrettyFunc "bvMul" [ stringPrettyArg (ppBV sm), exprPrettyArg e ] ]
                ppBV = BV.ppHex w

        SR.SemiRingBVRepr SR.BVBitsRepr w -> prettyApp "bvXor" (WSum.eval (++) ppEntry ppConstant s)
          where ppConstant (BV.BV 0) = []
                ppConstant c = [ stringPrettyArg (ppBV c) ]
                ppEntry sm e
                  | sm == BV.maxUnsigned w = [ exprPrettyArg e ]
                  | otherwise = [ PrettyFunc "bvAnd" [ stringPrettyArg (ppBV sm), exprPrettyArg e ] ]
                ppBV = BV.ppHex w

    SemiRingProd pd ->
      case WSum.prodRepr pd of
        SR.SemiRingRealRepr ->
          prettyApp "realProd" $ fromMaybe [] (WSum.prodEval (++) ((:[]) . exprPrettyArg) pd)
        SR.SemiRingIntegerRepr ->
          prettyApp "intProd" $ fromMaybe [] (WSum.prodEval (++) ((:[]) . exprPrettyArg) pd)
        SR.SemiRingNatRepr ->
          prettyApp "natProd" $ fromMaybe [] (WSum.prodEval (++) ((:[]) . exprPrettyArg) pd)
        SR.SemiRingBVRepr SR.BVArithRepr _w ->
          prettyApp "bvProd" $ fromMaybe [] (WSum.prodEval (++) ((:[]) . exprPrettyArg) pd)
        SR.SemiRingBVRepr SR.BVBitsRepr _w ->
          prettyApp "bvAnd" $ fromMaybe [] (WSum.prodEval (++) ((:[]) . exprPrettyArg) pd)


    RealDiv x y -> ppSExpr "divReal" [x, y]
    RealSqrt x  -> ppSExpr "sqrt" [x]

    Pi -> prettyApp "pi" []
    RealSin x     -> ppSExpr "sin" [x]
    RealCos x     -> ppSExpr "cos" [x]
    RealATan2 x y -> ppSExpr "atan2" [x, y]
    RealSinh x    -> ppSExpr "sinh" [x]
    RealCosh x    -> ppSExpr "cosh" [x]

    RealExp x -> ppSExpr "exp" [x]
    RealLog x -> ppSExpr "log" [x]

    --------------------------------
    -- Bitvector operations

    BVUnaryTerm u -> prettyApp "bvUnary" (concatMap go $ UnaryBV.unsignedEntries u)
      where go :: (Integer, e BaseBoolType) -> [PrettyArg e]
            go (k,v) = [ exprPrettyArg v, showPrettyArg k ]
    BVOrBits _ bs -> prettyApp "bvOr" $ map exprPrettyArg $ bvOrToList bs

    BVConcat _ x y -> prettyApp "bvConcat" [exprPrettyArg x, exprPrettyArg y]
    BVSelect idx n x -> prettyApp "bvSelect" [showPrettyArg idx, showPrettyArg n, exprPrettyArg x]
    BVUdiv _ x y -> ppSExpr "bvUdiv" [x, y]
    BVUrem _ x y -> ppSExpr "bvUrem" [x, y]
    BVSdiv _ x y -> ppSExpr "bvSdiv" [x, y]
    BVSrem _ x y -> ppSExpr "bvSrem" [x, y]

    BVShl  _ x y -> ppSExpr "bvShl" [x, y]
    BVLshr _ x y -> ppSExpr "bvLshr" [x, y]
    BVAshr _ x y -> ppSExpr "bvAshr" [x, y]
    BVRol  _ x y -> ppSExpr "bvRol" [x, y]
    BVRor  _ x y -> ppSExpr "bvRor" [x, y]

    BVZext w x -> prettyApp "bvZext"   [showPrettyArg w, exprPrettyArg x]
    BVSext w x -> prettyApp "bvSext"   [showPrettyArg w, exprPrettyArg x]
    BVFill w p -> prettyApp "bvFill"   [showPrettyArg w, exprPrettyArg p]

    BVPopcount w x -> prettyApp "bvPopcount" [showPrettyArg w, exprPrettyArg x]
    BVCountLeadingZeros w x -> prettyApp "bvCountLeadingZeros" [showPrettyArg w, exprPrettyArg x]
    BVCountTrailingZeros w x -> prettyApp "bvCountTrailingZeros" [showPrettyArg w, exprPrettyArg x]

    --------------------------------
    -- Float operations
    FloatPZero _ -> prettyApp "floatPZero" []
    FloatNZero _ -> prettyApp "floatNZero" []
    FloatNaN _ -> prettyApp "floatNaN" []
    FloatPInf _ -> prettyApp "floatPInf" []
    FloatNInf _ -> prettyApp "floatNInf" []
    FloatNeg _ x -> ppSExpr "floatNeg" [x]
    FloatAbs _ x -> ppSExpr "floatAbs" [x]
    FloatSqrt _ r x -> ppSExpr (Text.pack $ "floatSqrt " <> show r) [x]
    FloatAdd _ r x y -> ppSExpr (Text.pack $ "floatAdd " <> show r) [x, y]
    FloatSub _ r x y -> ppSExpr (Text.pack $ "floatSub " <> show r) [x, y]
    FloatMul _ r x y -> ppSExpr (Text.pack $ "floatMul " <> show r) [x, y]
    FloatDiv _ r x y -> ppSExpr (Text.pack $ "floatDiv " <> show r) [x, y]
    FloatRem _ x y -> ppSExpr "floatRem" [x, y]
    FloatMin _ x y -> ppSExpr "floatMin" [x, y]
    FloatMax _ x y -> ppSExpr "floatMax" [x, y]
    FloatFMA _ r x y z -> ppSExpr (Text.pack $ "floatFMA " <> show r) [x, y, z]
    FloatFpEq x y -> ppSExpr "floatFpEq" [x, y]
    FloatFpNe x y -> ppSExpr "floatFpNe" [x, y]
    FloatLe x y -> ppSExpr "floatLe" [x, y]
    FloatLt x y -> ppSExpr "floatLt" [x, y]
    FloatIsNaN x -> ppSExpr "floatIsNaN" [x]
    FloatIsInf x -> ppSExpr "floatIsInf" [x]
    FloatIsZero x -> ppSExpr "floatIsZero" [x]
    FloatIsPos x -> ppSExpr "floatIsPos" [x]
    FloatIsNeg x -> ppSExpr "floatIsNeg" [x]
    FloatIsSubnorm x -> ppSExpr "floatIsSubnorm" [x]
    FloatIsNorm x -> ppSExpr "floatIsNorm" [x]
    FloatCast _ r x -> ppSExpr (Text.pack $ "floatCast " <> show r) [x]
    FloatRound _ r x -> ppSExpr (Text.pack $ "floatRound " <> show r) [x]
    FloatFromBinary _ x -> ppSExpr "floatFromBinary" [x]
    FloatToBinary _ x -> ppSExpr "floatToBinary" [x]
    BVToFloat _ r x -> ppSExpr (Text.pack $ "bvToFloat " <> show r) [x]
    SBVToFloat _ r x -> ppSExpr (Text.pack $ "sbvToFloat " <> show r) [x]
    RealToFloat _ r x -> ppSExpr (Text.pack $ "realToFloat " <> show r) [x]
    FloatToBV _ r x -> ppSExpr (Text.pack $ "floatToBV " <> show r) [x]
    FloatToSBV _ r x -> ppSExpr (Text.pack $ "floatToSBV " <> show r) [x]
    FloatToReal x -> ppSExpr "floatToReal " [x]

    -------------------------------------
    -- Arrays

    ArrayMap _ _ m d ->
        prettyApp "arrayMap" (foldr ppEntry [exprPrettyArg d] (AUM.toList m))
      where ppEntry (k,e) l = showPrettyArg k : exprPrettyArg e : l
    ConstantArray _ _ v ->
      prettyApp "constArray" [exprPrettyArg v]
    SelectArray _ a i ->
      prettyApp "select" (exprPrettyArg a : exprPrettyIndices i)
    UpdateArray _ _ a i v ->
      prettyApp "update" ([exprPrettyArg a] ++ exprPrettyIndices i ++ [exprPrettyArg v])

    ------------------------------------------------------------------------
    -- Conversions.

    NatToInteger x  -> ppSExpr "natToInteger" [x]
    IntegerToReal x -> ppSExpr "integerToReal" [x]
    BVToNat x       -> ppSExpr "bvToNat" [x]
    BVToInteger  x  -> ppSExpr "bvToInteger" [x]
    SBVToInteger x  -> ppSExpr "sbvToInteger" [x]

    RoundReal x -> ppSExpr "round" [x]
    RoundEvenReal x -> ppSExpr "roundEven" [x]
    FloorReal x -> ppSExpr "floor" [x]
    CeilReal  x -> ppSExpr "ceil"  [x]

    IntegerToNat x   -> ppSExpr "integerToNat" [x]
    IntegerToBV x w -> prettyApp "integerToBV" [exprPrettyArg x, showPrettyArg w]

    RealToInteger x   -> ppSExpr "realToInteger" [x]

    ------------------------------------------------------------------------
    -- String operations

    StringIndexOf x y k ->
       prettyApp "string-index-of" [exprPrettyArg x, exprPrettyArg y, exprPrettyArg k]
    StringContains x y -> ppSExpr "string-contains" [x, y]
    StringIsPrefixOf x y -> ppSExpr "string-is-prefix-of" [x, y]
    StringIsSuffixOf x y -> ppSExpr "string-is-suffix-of" [x, y]
    StringSubstring _ x off len ->
       prettyApp "string-substring" [exprPrettyArg x, exprPrettyArg off, exprPrettyArg len]
    StringAppend _ xs -> prettyApp "string-append" (map f (SSeq.toList xs))
          where f (SSeq.StringSeqLiteral l) = showPrettyArg l
                f (SSeq.StringSeqTerm t)    = exprPrettyArg t
    StringLength x -> ppSExpr "string-length" [x]

    ------------------------------------------------------------------------
    -- Complex operations

    Cplx (r :+ i) -> ppSExpr "complex" [r, i]
    RealPart x -> ppSExpr "realPart" [x]
    ImagPart x -> ppSExpr "imagPart" [x]

    ------------------------------------------------------------------------
    -- SymStruct

    StructCtor _ flds -> prettyApp "struct" (toListFC exprPrettyArg flds)
    StructField s idx _ ->
      prettyApp "field" [exprPrettyArg s, showPrettyArg idx]



-- | Used to implement foldMapFc from traversal.
data Dummy (tp :: k)

instance Eq (Dummy tp) where
  _ == _ = True
instance EqF Dummy where
  eqF _ _ = True
instance TestEquality Dummy where
  testEquality x _y = case x of {}

instance Ord (Dummy tp) where
  compare _ _ = EQ
instance OrdF Dummy where
  compareF x _y = case x of {}

instance HashableF Dummy where
  hashWithSaltF _ _ = 0

instance HasAbsValue Dummy where
  getAbsValue _ = error "you made a magic Dummy value!"

instance FoldableFC App where
  foldMapFC f0 t = getConst (traverseApp (g f0) t)
    where g :: (f tp -> a) -> f tp -> Const a (Dummy tp)
          g f v = Const (f v)

traverseApp :: (Applicative m, OrdF f, Eq (f (BaseBoolType)), HashableF f, HasAbsValue f)
            => (forall tp. e tp -> m (f tp))
            -> App e utp -> m ((App f) utp)
traverseApp =
  $(structuralTraversal [t|App|]
    [ ( ConType [t|UnaryBV|] `TypeApp` AnyType `TypeApp` AnyType
      , [|UnaryBV.instantiate|]
      )
    , ( ConType [t|Ctx.Assignment BaseTypeRepr|] `TypeApp` AnyType
      , [|(\_ -> pure) |]
      )
    , ( ConType [t|WeightedSum|] `TypeApp` AnyType `TypeApp` AnyType
      , [| WSum.traverseVars |]
      )
    , ( ConType [t|BVOrSet|] `TypeApp` AnyType `TypeApp` AnyType
      , [| traverseBVOrSet |]
      )
    , ( ConType [t|SemiRingProduct|] `TypeApp` AnyType `TypeApp` AnyType
      , [| WSum.traverseProdVars |]
      )
    , ( ConType [t|AUM.ArrayUpdateMap|] `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType
      , [| AUM.traverseArrayUpdateMap |]
      )
    , ( ConType [t|SSeq.StringSeq|] `TypeApp` AnyType `TypeApp` AnyType
      , [| SSeq.traverseStringSeq |]
      )
    , ( ConType [t|BoolMap|] `TypeApp` AnyType
      , [| BM.traverseVars |]
      )
    , ( ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType
      , [|traverseFC|]
      )
    ]
   )

{-# NOINLINE appEqF #-}
-- | Check if two applications are equal.
appEqF ::
  (Eq (e BaseBoolType), Eq (e BaseRealType), HashableF e, HasAbsValue e, OrdF e) =>
  App e x -> App e y -> Maybe (x :~: y)
appEqF = $(structuralTypeEquality [t|App|]
           [ (TypeApp (ConType [t|NatRepr|]) AnyType, [|testEquality|])
           , (TypeApp (ConType [t|FloatPrecisionRepr|]) AnyType, [|testEquality|])
           , (TypeApp (ConType [t|BaseTypeRepr|]) AnyType, [|testEquality|])
           , (DataArg 0 `TypeApp` AnyType, [|testEquality|])
           , (ConType [t|UnaryBV|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|AUM.ArrayUpdateMap|] `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType
             , [|\x y -> if x == y then Just Refl else Nothing|])
           , (ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|Ctx.Index|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|StringInfoRepr|] `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|SR.SemiRingRepr|] `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|SR.OrderedSemiRingRepr|] `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|WSum.WeightedSum|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|SemiRingProduct|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|])
           ]
          )

instance (Eq (e BaseBoolType), Eq (e BaseRealType), HashableF e, HasAbsValue e, OrdF e) => Eq (App e tp) where
  x == y = isJust (testEquality x y)

instance (Eq (e BaseBoolType), Eq (e BaseRealType), HashableF e, HasAbsValue e, OrdF e) => TestEquality (App e) where
  testEquality = appEqF

{-# NOINLINE hashApp #-}
-- | Hash an an application.
hashApp ::
  (OrdF e, HashableF e, HasAbsValue e, Hashable (e BaseBoolType), Hashable (e BaseRealType)) =>
  Int -> App e s -> Int
hashApp = $(structuralHashWithSalt [t|App|]
               [(DataArg 0 `TypeApp` AnyType, [|hashWithSaltF|])]
           )

instance (OrdF e, HashableF e, HasAbsValue e, Hashable (e BaseBoolType), Hashable (e BaseRealType)) =>
  HashableF (App e) where
    hashWithSaltF = hashApp


-- | Return 'true' if an app represents a non-linear operation.
-- Controls whether the non-linear counter ticks upward in the
-- 'Statistics'.
isNonLinearApp :: App e tp -> Bool
isNonLinearApp app = case app of
  -- FIXME: These are just guesses; someone who knows what's actually
  -- slow in the solvers should correct them.

  SemiRingProd pd
    | SR.SemiRingBVRepr SR.BVBitsRepr _ <- WSum.prodRepr pd -> False
    | otherwise -> True

  NatDiv {} -> True
  NatMod {} -> True
  IntDiv {} -> True
  IntMod {} -> True
  IntDivisible {} -> True
  RealDiv {} -> True
  RealSqrt {} -> True
  RealSin {} -> True
  RealCos {} -> True
  RealATan2 {} -> True
  RealSinh {} -> True
  RealCosh {} -> True
  RealExp {} -> True
  RealLog {} -> True
  BVUdiv {} -> True
  BVUrem {} -> True
  BVSdiv {} -> True
  BVSrem {} -> True
  FloatSqrt {} -> True
  FloatMul {} -> True
  FloatDiv {} -> True
  FloatRem {} -> True
  _ -> False



instance TestEquality e => Eq (NonceApp t e tp) where
  x == y = isJust (testEquality x y)

instance TestEquality e => TestEquality (NonceApp t e) where
  testEquality =
    $(structuralTypeEquality [t|NonceApp|]
           [ (DataArg 0 `TypeApp` AnyType, [|testEquality|])
           , (DataArg 1 `TypeApp` AnyType, [|testEquality|])
           , ( ConType [t|BaseTypeRepr|] `TypeApp` AnyType
             , [|testEquality|]
             )
           , ( ConType [t|Nonce|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|]
             )
           , ( ConType [t|ExprBoundVar|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|]
             )
           , ( ConType [t|ExprSymFn|] `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType
              , [|testExprSymFnEq|]
              )
           , ( ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|]
             )
           ]
          )

instance HashableF e => HashableF (NonceApp t e) where
  hashWithSaltF = $(structuralHashWithSalt [t|NonceApp|]
                      [ (DataArg 1 `TypeApp` AnyType, [|hashWithSaltF|]) ])

instance FunctorFC (NonceApp t)  where
  fmapFC = fmapFCDefault

instance FoldableFC (NonceApp t) where
  foldMapFC = foldMapFCDefault

traverseArrayResultWrapper
  :: Functor m
  => (forall tp . e tp -> m (f tp))
     -> ArrayResultWrapper e (idx ::> itp) c
     -> m (ArrayResultWrapper f (idx ::> itp) c)
traverseArrayResultWrapper f (ArrayResultWrapper a) =
  ArrayResultWrapper <$> f a

traverseArrayResultWrapperAssignment
  :: Applicative m
  => (forall tp . e tp -> m (f tp))
     -> Ctx.Assignment (ArrayResultWrapper e (idx ::> itp)) c
     -> m (Ctx.Assignment (ArrayResultWrapper f (idx ::> itp)) c)
traverseArrayResultWrapperAssignment f = traverseFC (\e -> traverseArrayResultWrapper f e)

traverseSymFnInfo :: Applicative m =>
  (forall u. f u  -> m (g u)) ->
  SymFnInfo t f ctx ret -> m (SymFnInfo t g ctx ret)
traverseSymFnInfo f x = case x of
  UninterpFnInfo ctx ret -> pure (UninterpFnInfo ctx ret)
  DefinedFnInfo args body policy ->
    (\body' -> DefinedFnInfo args body' policy) <$> f body
  MatlabSolverFnInfo mfn args body -> 
    MatlabSolverFnInfo <$> traverseMatlabSolverFn f mfn <*> pure args <*> f body

traverseExprSymFn :: Applicative m =>
  (forall u. f u  -> m (g u)) ->
  ExprSymFn t f ctx ret -> m (ExprSymFn t g ctx ret)
traverseExprSymFn f (ExprSymFn fnid nm info loc) =
  (\info' -> ExprSymFn fnid nm info' loc) <$> traverseSymFnInfo f info

instance TraversableFC (NonceApp t) where
  traverseFC =
    $(structuralTraversal [t|NonceApp|]
      [ ( ConType [t|Ctx.Assignment|]
          `TypeApp` (ConType [t|ArrayResultWrapper|] `TypeApp` AnyType `TypeApp` AnyType)
          `TypeApp` AnyType
        , [|traverseArrayResultWrapperAssignment|]
        )
      , ( ConType [t|ExprSymFn|] `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType
        , [|traverseExprSymFn|]
        )
      , ( ConType [t|Ctx.Assignment|] `TypeApp` ConType [t|BaseTypeRepr|] `TypeApp` AnyType
        , [|\_ -> pure|]
        )
      , ( ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType
        , [|traverseFC|]
        )
      ]
     )

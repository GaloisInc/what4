{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Bool (boolTests) where

import Control.Monad (unless)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans (lift)
import Data.Coerce (coerce)
import Data.Map qualified as Map
import Data.Maybe qualified as Maybe
import Data.Monoid (All(getAll, All))
import Data.Parameterized.Map qualified as MapF
import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some (Some(Some))
import Hedgehog (GenT)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Internal.Property qualified as HG
import Hedgehog qualified as HG
import Test.Tasty.Hedgehog qualified as THG
import Test.Tasty qualified as T
import What4.Expr.BoolMap qualified as BM
import What4.Expr.Builder
import What4.Expr (EmptyExprBuilderState(EmptyExprBuilderState))
import What4.Interface

-- | Boolean expressions that should always normalize
data BExpr a
  = -- 0-ary
    Lit !Bool
  | Var !a
    -- unary
  | Not !(BExpr a)
    -- binary
  | And !(BExpr a) !(BExpr a)
  | Eq !(BExpr a) !(BExpr a)
  | Or !(BExpr a) !(BExpr a)
  | Xor !(BExpr a) !(BExpr a)
    -- tertiary
  | Ite !(BExpr a) !(BExpr a) !(BExpr a)
  deriving Show

genBExpr :: HG.MonadGen m => m a -> m (BExpr a)
genBExpr var =
  Gen.recursive
    Gen.choice
    [ -- 0-ary
      Lit <$> Gen.bool
    , Var <$> var
    ]
    [ -- unary
      Not <$> genBExpr var
      -- binary
    , And <$> genBExpr var <*> genBExpr var
    -- TODO: Generate Eq
    -- , Eq <$> genBExpr var <*> genBExpr var
    , Or <$> genBExpr var <*> genBExpr var
    -- TODO: Generate Ite
    -- , Ite <$> genBExpr var <*> genBExpr var <*> genBExpr var
    ]

newtype Valuation t
  = Valuation { getValuation :: Map.Map (ExprBoundVar t BaseBoolType) Bool }
  deriving Show

getValue :: ExprBoundVar t BaseBoolType -> Valuation t -> Bool
getValue v = Maybe.fromJust . Map.lookup v . getValuation

genFreshVar ::
  (HG.MonadGen m, MonadIO m) =>
  ExprBuilder t st fs ->
  State.StateT (Valuation t) m (ExprBoundVar t BaseBoolType)
genFreshVar sym = do
  v <- lift (liftIO (freshConstant sym (safeSymbol "b") BaseBoolRepr))
  case v of
    BoundVarExpr v' -> do
      b <- Gen.bool
      State.modify (coerce (Map.insert v' b))
      pure v'
    _ -> error "Not a bound variable?"

-- | Generate a new variable ('genFreshVar') or reuse an existing one
genVar ::
  (HG.MonadGen m, MonadIO m) =>
  ExprBuilder t st fs ->
  State.StateT (Valuation t) m (ExprBoundVar t BaseBoolType)
genVar sym = do
  b <- Gen.bool
  if b
    then genFreshVar sym
    else do
      vs <- State.gets (Map.toList . getValuation)
      case vs of
        [] -> genFreshVar sym
        _ -> Gen.choice (map (pure . fst) vs)

doGenExpr ::
  ExprBuilder t st fs ->
  GenT IO (BExpr (ExprBoundVar t BaseBoolType), Valuation t)
doGenExpr sym =
  let vars0 = Valuation Map.empty in
  State.runStateT (genBExpr @(State.StateT _ (GenT IO)) (genVar @(GenT IO) sym)) vars0

interp ::
  IsExprBuilder sym =>
  sym ->
  (a -> IO (SymExpr sym BaseBoolType)) ->
  BExpr a ->
  IO (SymExpr sym BaseBoolType)
interp sym var = go
  where
  go =
    \case
      Lit True -> pure (truePred sym)
      Lit False -> pure (falsePred sym)
      Var v -> var v
      Not e -> notPred sym =<< go e
      And l r -> do
        l' <- go l
        r' <- go r
        andPred sym l' r'
      Eq l r -> do
        l' <- go l
        r' <- go r
        eqPred sym l' r'
      Or l r -> do
        l' <- go l
        r' <- go r
        orPred sym l' r'
      Xor l r -> do
        l' <- go l
        r' <- go r
        xorPred sym l' r'
      Ite c l r -> do
        c' <- go c
        l' <- go l
        r' <- go r
        itePred sym c' l' r'

eval :: Applicative f => (a -> f Bool) -> BExpr a -> f Bool
eval var = go
  where
  ite c l r = if c then l else r
  go =
    \case
      Lit True -> pure True
      Lit False -> pure False
      Var v -> var v
      Not e -> not <$> go e
      And l r -> (&&) <$> go l <*> go r
      Eq l r -> (==) <$> go l <*> go r
      Or l r -> (||) <$> go l <*> go r
      Xor l r -> (/=) <$> go l <*> go r
      Ite c l r -> ite <$> go c <*> go l <*> go r

getVar :: ExprBoundVar t BaseBoolType -> State.State (Valuation t) Bool
getVar v = State.gets (getValue v)

_interpVar ::
  ExprBuilder t st fs ->
  Valuation t ->
  ExprBoundVar t BaseBoolType ->
  IO (Expr t BaseBoolType)
_interpVar sym vs v =
  if getValue v vs
  then pure (truePred sym)
  else pure (falsePred sym)

uninterpVar :: ExprBoundVar t BaseBoolType -> Expr t BaseBoolType
uninterpVar = BoundVarExpr

isNormalMap :: BM.ConjMap (Expr t) -> Bool
isNormalMap = getAll . BM.foldMapVars (All . isNormalMapEntry) . BM.getConjMap
  where
    isNormalMapEntry =
      \case
        BoolExpr {} -> True
        BoundVarExpr {} -> True
        AppExpr ae ->
          case appExprApp ae of
            NotPred (BoundVarExpr {}) -> True
            -- An OR inside an AND
            NotPred (asApp -> Just ConjPred {}) -> True
            -- TODO: We do *not* want to see an un-negated map in here
            ConjPred {} -> True
            _ -> False
        _ -> False

isNormal :: Expr t BaseBoolType -> Bool
isNormal =
  \case
    BoolExpr {} -> True
    BoundVarExpr {} -> True
    AppExpr ae ->
      case appExprApp ae of
        ConjPred cm -> isNormalMap cm
        -- NotPred (asApp -> Just (ConjPred {})) -> True
        NotPred (asApp -> Just (ConjPred cm)) -> isNormalMap cm
        -- NotPred (asApp -> Just (BaseEq BaseBoolRepr (BoundVarExpr {}) r)) -> isNormal r
        -- NotPred (asApp -> Just (BaseEq BaseBoolRepr l (BoundVarExpr {}))) -> isNormal l
        NotPred (BoundVarExpr {}) -> True
        _ -> False
    _ -> False

boolTests :: T.TestTree
boolTests =
  T.testGroup
    "boolean normalization tests"
    [ THG.testProperty "boolean normalization" $
        HG.property $ do
          Some ng <- liftIO newIONonceGenerator
          sym <- liftIO (newExprBuilder FloatIEEERepr EmptyExprBuilderState ng)
          (e, _vars) <- HG.forAllT (doGenExpr sym)
          e' <- liftIO (interp sym (pure . uninterpVar) e)
          let ok = isNormal e'
          unless ok $
            liftIO (putStrLn ("Not normalized:\n" ++ show (printSymExpr e')))
          HG.assert ok
    , THG.testProperty "boolean normalization 2" $
        HG.property $ do
          Some ng <- liftIO newIONonceGenerator
          sym <- liftIO (newExprBuilder FloatIEEERepr EmptyExprBuilderState ng)
          (e, vars) <- HG.forAllT (doGenExpr sym)
          let expected = State.evalState (eval getVar e) vars
          e' <- liftIO (interp sym (pure . uninterpVar) e)
          let vs = Map.toList (getValuation vars)
          let substs = foldr (\(v, b) -> MapF.insert v (if b then truePred sym else falsePred sym)) MapF.empty vs
          e'' <- liftIO (substituteBoundVars sym substs e')
          case asConstantPred e'' of
            Just actual -> actual HG.=== expected
            Nothing -> HG.failure
    ]

{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Bool where

import Control.Monad (unless, when)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans (lift)
import Data.Coerce (coerce)
import Data.Either (isRight)
import Data.Foldable (traverse_)
import Data.Map qualified as Map
import Data.Parameterized.Map qualified as MapF
import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some (Some(Some))
import Hedgehog (GenT)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Internal.Gen qualified as HG
import Hedgehog.Internal.Property qualified as HG
import Test.Tasty.Hedgehog qualified as THG
import Test.Tasty qualified as T
import What4.Expr.BoolMap qualified as BM
import What4.Expr.Builder
import What4.Expr (EmptyExprBuilderState(EmptyExprBuilderState))
import What4.Interface

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
    -- TODO: Generate Eq, Xor.
    --
    -- This would require updating 'isNormal' to take these into account.
    --
    -- , Eq <$> genBExpr var <*> genBExpr var
    , Or <$> genBExpr var <*> genBExpr var
    -- , Xor <$> genBExpr var <*> genBExpr var
    , Ite <$> genBExpr var <*> genBExpr var <*> genBExpr var
    ]

newtype Valuation t
  = Valuation { getValuation :: Map.Map (ExprBoundVar t BaseBoolType) Bool }
  deriving Show

getValue :: ExprBoundVar t BaseBoolType -> Valuation t -> Bool
getValue v vs =
  case Map.lookup v (getValuation vs) of
    Nothing -> error "getValue: bad variable"
    Just b -> b

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

toSymExpr ::
  IsExprBuilder sym =>
  sym ->
  -- | How to handle variables
  (a -> IO (SymExpr sym BaseBoolType)) ->
  BExpr a ->
  IO (SymExpr sym BaseBoolType)
toSymExpr sym var = go
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

-- | For use with 'toSymExpr', to leave variables uninterpreted
uninterpVar :: ExprBoundVar t BaseBoolType -> Expr t BaseBoolType
uninterpVar = BoundVarExpr

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

-- | For use with 'eval', to interpret variables
getVar :: ExprBoundVar t BaseBoolType -> State.State (Valuation t) Bool
getVar v = State.gets (getValue v)

isNot :: Expr t BaseBoolType -> Bool
isNot e =
  case e of
    AppExpr ae ->
      case appExprApp ae of
        NotPred {} -> True
        _ -> False
    _ -> False

isNormalIte ::
  ExprBuilder t st fs ->
  Expr t BaseBoolType -> 
  Expr t BaseBoolType -> 
  Expr t BaseBoolType -> 
  Either String ()
isNormalIte sym c l r = do
  isNormal sym c
  isNormal sym l
  isNormal sym r
  when (isNot c) (Left "negated ite condition")
  when (c == l) (Left "ite cond == LHS")
  when (c == r) (Left "ite cond == RHS")
  when (c == truePred sym) (Left "ite cond == true")
  when (c == falsePred sym) (Left "ite cond == false")

isNormalConjunct ::
  ExprBuilder t st fs ->
  Expr t BaseBoolType ->
  BM.Polarity ->
  Either String ()
isNormalConjunct sym expr pol =
  case expr of
    BoolExpr {} -> Left "boolean literal inside conjunction"
    BoundVarExpr {} -> Right ()
    AppExpr ae ->
      case appExprApp ae of
        NotPred {} -> Left "not should be expressed via polarity"
        -- This must be an OR, if it is an AND it should be combined with
        -- its parent
        ConjPred cm' -> do
          when (pol == BM.Positive) (Left "and inside and")
          -- Note that it is possible to have ORs inside ORs, e.g., if the outer
          -- OR used to be an AND but was negated.
          isNormalMap sym cm'
        BaseIte BaseBoolRepr _sz c l r -> isNormalIte sym c l r
        _ -> Left "non-normal app in conjunct"
    _ -> Left "non-normal expr in conjunct"

isNormalMap :: ExprBuilder t st fs -> BM.ConjMap (Expr t) -> Either String ()
isNormalMap sym cm =
  case BM.viewConjMap cm of
    BM.ConjTrue -> Left "empty conjunction map"
    BM.ConjFalse -> Left "inconsistent conjunction map"
    BM.Conjuncts conjs -> traverse_ (uncurry (isNormalConjunct sym)) conjs

-- | Is this boolean expression sufficiently normalized?
isNormal :: ExprBuilder t st fs -> Expr t BaseBoolType -> Either String ()
isNormal sym =
  \case
    BoolExpr {} -> Right ()
    BoundVarExpr {} -> Right ()
    AppExpr ae ->
      case appExprApp ae of
        NotPred (asApp -> Just NotPred {}) -> Left "double negation"
        NotPred e -> isNormal sym e
        ConjPred cm -> isNormalMap sym cm
        BaseIte BaseBoolRepr _sz c l r -> isNormalIte sym c l r
        _ -> Left "non-normal app"
    _ -> Left "non-normal expr"

boolTests :: T.TestTree
boolTests =
  T.testGroup
    "boolean normalization tests"
    [ -- Test that the rewrite rules rewrite expressions into a sufficiently
      -- normal form (defined by 'isNormal').
      THG.testProperty "boolean rewrites normalize" $
        HG.property $ do
          Some ng <- liftIO newIONonceGenerator
          sym <- liftIO (newExprBuilder FloatIEEERepr EmptyExprBuilderState ng)
          (e, _vars) <- HG.forAllT (doGenExpr sym)
          e' <- liftIO (toSymExpr sym (pure . uninterpVar) e)
          let ok = isNormal sym e'
          unless (isRight ok) $
            liftIO (putStrLn ("Not normalized:\n" ++ show (printSymExpr e')))
          ok HG.=== Right ()
    , THG.testProperty "boolean rewrites preserve semantics" $
        HG.property $ do
          Some ng <- liftIO newIONonceGenerator
          sym <- liftIO (newExprBuilder FloatIEEERepr EmptyExprBuilderState ng)
          (e, vars) <- HG.forAllT (doGenExpr sym)
          -- Concretely evaluate the `BExpr` to get the expected semantics.
          let expected = State.evalState (eval getVar e) vars
          -- Generate a `Expr` with uninterpreted variables. It is important to
          -- not interpret the variables into `truePred` and `falsePred` here,
          -- to avoid only hitting the `asConstantPred` cases in the rewrites.
          e' <- liftIO (toSymExpr sym (pure . uninterpVar) e)
          -- Finally, substitute values in for the variables, simplifying the
          -- `Expr` along the way until we get a concrete boolean.
          let vs = Map.toList (getValuation vars)
          let substs = foldr (\(v, b) -> MapF.insert v (if b then truePred sym else falsePred sym)) MapF.empty vs
          e'' <- liftIO (substituteBoundVars sym substs e')
          -- Check that the `BExpr` and `Expr` agreed on the semantics.
          case asConstantPred e'' of
            Just actual -> actual HG.=== expected
            Nothing -> HG.failure
    ]

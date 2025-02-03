-- See what percentage of randomly-generated boolean expressions can be
-- completely simplified away. Higher is better. This is one mechanism for
-- evaluating rewrite rules.

{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module Main (main) where

import Control.Monad (foldM)
import Control.Monad.State.Strict qualified as State
import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some (Some(Some))
import Data.Parameterized.TraversableFC (traverseFC_)
import Hedgehog.Internal.Gen qualified as HG
import Hedgehog.Internal.Tree qualified as HG
import Hedgehog qualified as HG
import What4.Expr.Builder
import What4.Expr (EmptyExprBuilderState(EmptyExprBuilderState))
import What4.Interface

import Bool

-- | Get the size of an expression. Lower is better.
sz :: Expr t tp -> Int
sz =
  \case
    SemiRingLiteral {} -> 1
    BoolExpr {} -> 1
    FloatExpr {} -> 1
    StringExpr {} -> 1
    AppExpr ae ->
      State.execState (traverseFC_ (\e -> State.modify (+ sz e)) (appExprApp ae)) 1
    NonceAppExpr nae ->
      State.execState (traverseFC_ (\e -> State.modify (+ sz e)) (nonceExprApp nae)) 1
    BoundVarExpr {} -> 1

main :: IO ()
main = do
  Some ng <- newIONonceGenerator
  sym <- newExprBuilder FloatIEEERepr EmptyExprBuilderState ng
  let eliminated i = do
        x <- HG.runTreeT (HG.evalGenT (HG.Size 100) (HG.Seed i 1) (doGenExpr sym))
        case HG.nodeValue x of
          Nothing -> error "whoops"
          Just (bExpr, _vars) -> do
            e <- toSymExpr sym (pure . uninterpVar) bExpr
            -- Audit the quality of the generated expressions:
            -- putStrLn "--------------------------------------"
            -- putStrLn (show bExpr)
            -- putStrLn "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"
            -- putStrLn (show (printSymExpr e))
            -- putStrLn "______________________________________"
            -- putStrLn (show (sz e))
            case asConstantPred e of
              Just {} -> pure (1, sz e)
              Nothing -> pure (0, sz e)
  let total = 20000
  let count (accFull, accSize) (full, size) = (accFull + full, accSize + size)
  (full, size) <- foldM (\acc seed -> count acc <$> eliminated seed) (0 :: Int, 0 :: Int) [0..total]
  putStrLn ("Fully eliminated " ++ show full ++ "/" ++ show total)
  putStrLn ("Total size: " ++ show size)

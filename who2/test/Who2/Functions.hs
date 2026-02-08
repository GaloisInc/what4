{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Who2.Functions (tests) where

import Data.List (sort)
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString.Lazy as BSL
import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.NatRepr (knownNat)
import Data.Parameterized.Some (Some(Some))
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.Text.Lazy as Text.Lazy
import qualified Data.Text.Lazy.Builder as Builder
import System.Directory (listDirectory)
import System.Exit (ExitCode(..))
import System.FilePath ((</>), (<.>), takeExtension, dropExtension)
import System.Process (readProcessWithExitCode)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (testCase, assertBool)

import qualified What4.BaseTypes as BT
import qualified What4.Interface as WI
import qualified What4.Symbol as WS
import qualified What4.Protocol.SMTLib2.Syntax as SMT2

import qualified Who2.Builder as Who2B
import qualified Who2.Protocol.SMTLib2 as SMTWho2

-- | Helper to extract Right from Either with better error message
fromRight' :: Show e => Either e a -> a
fromRight' (Right x) = x
fromRight' (Left e) = error $ "userSymbol failed: " ++ show e

-- | Main test entry point
tests :: IO TestTree
tests = do
  z3Tests <- discoverZ3ValidationTests "test-data/functions"
  return $ testGroup "Function Applications"
    [ smtLib2Tests
    , definedFunctionTests
    , testGroup "Z3 Validation" z3Tests
    ]

-- | SMT-Lib2 serialization tests
smtLib2Tests :: TestTree
smtLib2Tests = testGroup "SMT-Lib2 Serialization"
  [ goldenTest "fn-unary-bv8-to-bv8" $ \sym -> do
      let symbol = fromRight' $ WS.userSymbol "f"
      let argTypes = Ctx.empty Ctx.:> BT.BaseBVRepr (knownNat @8)
      let retType = BT.BaseBVRepr (knownNat @8)
      fn <- WI.freshTotalUninterpFn sym symbol argTypes retType
      arg <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 42)
      WI.applySymFn sym fn (Ctx.empty Ctx.:> arg)

  , goldenTest "fn-binary-bv16-to-bv16" $ \sym -> do
      let symbol = fromRight' $ WS.userSymbol "add"
      let argTypes = Ctx.empty Ctx.:> BT.BaseBVRepr (knownNat @16) Ctx.:> BT.BaseBVRepr (knownNat @16)
      let retType = BT.BaseBVRepr (knownNat @16)
      fn <- WI.freshTotalUninterpFn sym symbol argTypes retType
      arg1 <- WI.bvLit sym (knownNat @16) (BV.mkBV knownNat 100)
      arg2 <- WI.bvLit sym (knownNat @16) (BV.mkBV knownNat 200)
      WI.applySymFn sym fn (Ctx.empty Ctx.:> arg1 Ctx.:> arg2)

  , goldenTest "fn-bv32-to-bool" $ \sym -> do
      let symbol = fromRight' $ WS.userSymbol "isPositive"
      let argTypes = Ctx.empty Ctx.:> BT.BaseBVRepr (knownNat @32)
      let retType = BT.BaseBoolRepr
      fn <- WI.freshTotalUninterpFn sym symbol argTypes retType
      arg <- WI.bvLit sym (knownNat @32) (BV.mkBV knownNat 42)
      WI.applySymFn sym fn (Ctx.empty Ctx.:> arg)

  , goldenTest "fn-nested-application" $ \sym -> do
      -- Create f :: BV8 -> BV8
      let fSymbol = fromRight' $ WS.userSymbol "f"
      let argTypes = Ctx.empty Ctx.:> BT.BaseBVRepr (knownNat @8)
      let retType = BT.BaseBVRepr (knownNat @8)
      f <- WI.freshTotalUninterpFn sym fSymbol argTypes retType

      -- Create g :: BV8 -> BV8
      let gSymbol = fromRight' $ WS.userSymbol "g"
      g <- WI.freshTotalUninterpFn sym gSymbol argTypes retType

      -- Compute g(f(x)) where x = 10
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 10)
      fx <- WI.applySymFn sym f (Ctx.empty Ctx.:> x)
      WI.applySymFn sym g (Ctx.empty Ctx.:> fx)

  , goldenTest "fn-mixed-with-operations" $ \sym -> do
      -- Create f :: BV8 -> BV8
      let symbol = fromRight' $ WS.userSymbol "f"
      let argTypes = Ctx.empty Ctx.:> BT.BaseBVRepr (knownNat @8)
      let retType = BT.BaseBVRepr (knownNat @8)
      f <- WI.freshTotalUninterpFn sym symbol argTypes retType

      -- Compute f(x) + y where x = 10, y = 20
      x <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 10)
      y <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 20)
      fx <- WI.applySymFn sym f (Ctx.empty Ctx.:> x)
      WI.bvAdd sym fx y

  , goldenTest "fn-with-symbolic-args" $ \sym -> do
      -- Create f :: BV32 x BV32 -> Bool
      let symbol = fromRight' $ WS.userSymbol "equal"
      let argTypes = Ctx.empty Ctx.:> BT.BaseBVRepr (knownNat @32) Ctx.:> BT.BaseBVRepr (knownNat @32)
      let retType = BT.BaseBoolRepr
      f <- WI.freshTotalUninterpFn sym symbol argTypes retType

      -- Create symbolic variables
      let xSymbol = fromRight' $ WS.userSymbol "x"
      let ySymbol = fromRight' $ WS.userSymbol "y"
      x <- WI.freshConstant sym xSymbol (BT.BaseBVRepr (knownNat @32))
      y <- WI.freshConstant sym ySymbol (BT.BaseBVRepr (knownNat @32))

      -- Apply function to symbolic args
      WI.applySymFn sym f (Ctx.empty Ctx.:> x Ctx.:> y)
  ]

-- | Defined function tests
definedFunctionTests :: TestTree
definedFunctionTests = testGroup "Defined Functions"
  [ goldenTest "def-fn-simple-add" $ \sym -> do
      -- Create bound variables for parameters
      let xSymbol = fromRight' $ WS.userSymbol "x"
      let ySymbol = fromRight' $ WS.userSymbol "y"
      xVar <- WI.freshBoundVar sym xSymbol (BT.BaseBVRepr (knownNat @8))
      yVar <- WI.freshBoundVar sym ySymbol (BT.BaseBVRepr (knownNat @8))

      -- Create the body: x + y
      let xExpr = WI.varExpr sym xVar
      let yExpr = WI.varExpr sym yVar
      body <- WI.bvAdd sym xExpr yExpr

      -- Define function add(x, y) = x + y
      let addSymbol = fromRight' $ WS.userSymbol "add"
      let vars = Ctx.empty Ctx.:> xVar Ctx.:> yVar
      addFn <- WI.definedFn sym addSymbol vars body WI.AlwaysUnfold

      -- Apply to concrete arguments: add(10, 20)
      arg1 <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 10)
      arg2 <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 20)
      WI.applySymFn sym addFn (Ctx.empty Ctx.:> arg1 Ctx.:> arg2)

  , goldenTest "def-fn-with-symbolic-args" $ \sym -> do
      -- Create bound variable for parameter
      let paramSymbol = fromRight' $ WS.userSymbol "n"
      paramVar <- WI.freshBoundVar sym paramSymbol (BT.BaseBVRepr (knownNat @16))

      -- Create the body: n * 2
      let nExpr = WI.varExpr sym paramVar
      two <- WI.bvLit sym (knownNat @16) (BV.mkBV knownNat 2)
      body <- WI.bvMul sym nExpr two

      -- Define function double(n) = n * 2
      let doubleSymbol = fromRight' $ WS.userSymbol "double"
      let vars = Ctx.empty Ctx.:> paramVar
      doubleFn <- WI.definedFn sym doubleSymbol vars body WI.AlwaysUnfold

      -- Apply to symbolic argument
      let argSymbol = fromRight' $ WS.userSymbol "input"
      arg <- WI.freshConstant sym argSymbol (BT.BaseBVRepr (knownNat @16))
      WI.applySymFn sym doubleFn (Ctx.empty Ctx.:> arg)

  , goldenTest "def-fn-nested-calls" $ \sym -> do
      -- Define increment(x) = x + 1
      let xSymbol = fromRight' $ WS.userSymbol "x"
      xVar <- WI.freshBoundVar sym xSymbol (BT.BaseBVRepr (knownNat @8))
      let xExpr = WI.varExpr sym xVar
      one <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 1)
      incBody <- WI.bvAdd sym xExpr one

      let incSymbol = fromRight' $ WS.userSymbol "increment"
      let incVars = Ctx.empty Ctx.:> xVar
      incFn <- WI.definedFn sym incSymbol incVars incBody WI.AlwaysUnfold

      -- Define addTwo(y) = increment(increment(y))
      let ySymbol = fromRight' $ WS.userSymbol "y"
      yVar <- WI.freshBoundVar sym ySymbol (BT.BaseBVRepr (knownNat @8))
      let yExpr = WI.varExpr sym yVar
      incY <- WI.applySymFn sym incFn (Ctx.empty Ctx.:> yExpr)
      incIncY <- WI.applySymFn sym incFn (Ctx.empty Ctx.:> incY)

      let addTwoSymbol = fromRight' $ WS.userSymbol "addTwo"
      let addTwoVars = Ctx.empty Ctx.:> yVar
      addTwoFn <- WI.definedFn sym addTwoSymbol addTwoVars incIncY WI.AlwaysUnfold

      -- Apply addTwo(5)
      five <- WI.bvLit sym (knownNat @8) (BV.mkBV knownNat 5)
      WI.applySymFn sym addTwoFn (Ctx.empty Ctx.:> five)

  , goldenTest "def-fn-mixed-with-uninterp" $ \sym -> do
      -- Create uninterpreted function hash :: BV32 -> BV32
      let hashSymbol = fromRight' $ WS.userSymbol "hash"
      let hashArgTypes = Ctx.empty Ctx.:> BT.BaseBVRepr (knownNat @32)
      let hashRetType = BT.BaseBVRepr (knownNat @32)
      hashFn <- WI.freshTotalUninterpFn sym hashSymbol hashArgTypes hashRetType

      -- Define wrapper(x) = hash(x) + 1
      let xSymbol = fromRight' $ WS.userSymbol "x"
      xVar <- WI.freshBoundVar sym xSymbol (BT.BaseBVRepr (knownNat @32))
      let xExpr = WI.varExpr sym xVar
      hashX <- WI.applySymFn sym hashFn (Ctx.empty Ctx.:> xExpr)
      one <- WI.bvLit sym (knownNat @32) (BV.mkBV knownNat 1)
      body <- WI.bvAdd sym hashX one

      let wrapperSymbol = fromRight' $ WS.userSymbol "wrapper"
      let vars = Ctx.empty Ctx.:> xVar
      wrapperFn <- WI.definedFn sym wrapperSymbol vars body WI.AlwaysUnfold

      -- Apply wrapper(42)
      arg <- WI.bvLit sym (knownNat @32) (BV.mkBV knownNat 42)
      WI.applySymFn sym wrapperFn (Ctx.empty Ctx.:> arg)

  , goldenTest "def-fn-boolean-result" $ \sym -> do
      -- Define isZero(x) = x == 0
      let xSymbol = fromRight' $ WS.userSymbol "x"
      xVar <- WI.freshBoundVar sym xSymbol (BT.BaseBVRepr (knownNat @16))
      let xExpr = WI.varExpr sym xVar
      zero <- WI.bvLit sym (knownNat @16) (BV.mkBV knownNat 0)
      body <- WI.bvEq sym xExpr zero

      let isZeroSymbol = fromRight' $ WS.userSymbol "isZero"
      let vars = Ctx.empty Ctx.:> xVar
      isZeroFn <- WI.definedFn sym isZeroSymbol vars body WI.AlwaysUnfold

      -- Apply isZero to symbolic variable
      let argSymbol = fromRight' $ WS.userSymbol "value"
      arg <- WI.freshConstant sym argSymbol (BT.BaseBVRepr (knownNat @16))
      WI.applySymFn sym isZeroFn (Ctx.empty Ctx.:> arg)
  ]

-- | Helper: create a golden test for a given operation
goldenTest :: String -> (forall t. Who2B.Builder t -> IO (WI.SymExpr (Who2B.Builder t) tp)) -> TestTree
goldenTest name mkExpr = goldenVsString name goldenFile $ do
  Some gen <- newIONonceGenerator
  sym <- Who2B.newBuilder gen
  expr <- mkExpr sym
  (decls, term) <- SMTWho2.mkSMTTermWithDecls expr
  let output = renderSMT2WithHeader decls term
  return $ BSL.fromStrict $ Text.encodeUtf8 output
  where
    goldenFile = "test-data" </> "functions" </> name <.> "smt2"

-- | Render a Term as SMT-Lib2 with proper header and function declarations
renderSMT2WithHeader :: [Text.Text] -> SMT2.Term -> Text.Text
renderSMT2WithHeader decls term =
  let header = "(set-logic QF_UFBV)\n"  -- Use QF_UFBV for uninterpreted functions + bitvectors
      declsSection = if null decls
                     then ""
                     else Text.intercalate "\n" decls <> "\n"
      -- Wrap term in a tautology (= term term) for Z3 validation
      assertion = Text.Lazy.toStrict $ Builder.toLazyText $ SMT2.renderTerm (SMT2.eq [term, term])
      checkSat = "(check-sat)\n"
  in Text.concat [header, declsSection, "(assert ", assertion, ")\n", checkSat]

-- | Discover Z3 validation tests from golden files directory
discoverZ3ValidationTests :: FilePath -> IO [TestTree]
discoverZ3ValidationTests dir = do
  files <- listDirectory dir
  let smt2Files = sort $ filter (\f -> takeExtension f == ".smt2") files
  return $ map (mkZ3Test dir) smt2Files
  where
    mkZ3Test :: FilePath -> FilePath -> TestTree
    mkZ3Test directory file =
      let name = dropExtension file
          goldenFile = directory </> file
      in testCase name $ do
        (exitCode, _, stderr) <- readProcessWithExitCode "z3" [goldenFile] ""
        case exitCode of
          ExitSuccess -> return ()
          ExitFailure code -> assertBool
            ("Z3 failed with exit code " ++ show code ++ "\nstderr: " ++ stderr)
            False

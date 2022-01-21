{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}

import           Control.Exception ( displayException, try, SomeException(..), fromException )
import           Control.Lens (folded)
import           Control.Monad ( forM, unless )
import           Control.Monad.Except ( runExceptT )
import           Data.BitVector.Sized ( mkBV )
import           Data.Char ( toLower )
import qualified Data.List as L
import           Data.Maybe ( fromMaybe )
import           Data.Text ( pack )
import           System.Environment ( lookupEnv )

import           ProbeSolvers
import           Test.Tasty
import           Test.Tasty.ExpectedFailure
import           Test.Tasty.HUnit

import           Data.Parameterized.Nonce
import           Data.Parameterized.Some

import           What4.Config
import           What4.Expr
import           What4.Interface
import           What4.Protocol.SMTLib2.Response ( strictSMTParsing )
import           What4.Protocol.SMTWriter ( parserStrictness, ResponseStrictness(..) )
import           What4.Protocol.VerilogWriter
import           What4.Solver

allAdapters :: [SolverAdapter State]
allAdapters =
  [ cvc4Adapter
  , yicesAdapter
  , z3Adapter
  , boolectorAdapter
  , externalABCAdapter
#ifdef TEST_STP
  , stpAdapter
#endif
  ] <> drealAdpt

drealAdpt :: [SolverAdapter State]
#ifdef TEST_DREAL
drealAdpt = [drealAdapter]
#else
drealAdpt = []
#endif


withSym ::
  SolverAdapter EmptyBuilderState ->
  (forall t . ExprBuilder t EmptyBuilderState (Flags FloatUninterpreted) -> IO a) ->
  IO a
withSym adpt pred_gen = withIONonceGenerator $ \gen ->
  do sym <- newExprBuilder FloatUninterpretedRepr EmptyBuilderState gen
     extendConfig (solver_adapter_config_options adpt) (getConfiguration sym)
     pred_gen sym

mkSmokeTest :: SolverAdapter EmptyBuilderState -> TestTree
mkSmokeTest adpt = testCase (solver_adapter_name adpt) $
  withSym adpt $ \sym ->
   do res <- smokeTest sym adpt
      case res of
        Nothing -> return ()
        Just ex -> fail $ displayException ex


----------------------------------------------------------------------

mkConfigTests :: [SolverAdapter State] -> [TestTree]
mkConfigTests adapters =
  [
    testGroup "deprecated configs" (deprecatedConfigTests adapters)
  , testGroup "strict parsing config" (strictParseConfigTests adapters)
  ]
  where
    wantOptSetFailure withText res = case res of
      Right r ->
        assertFailure ("Expected '" <> withText <>
                       "' but completed successfully with: " <> show r)
      Left err ->
        case fromException err of
          Just (e :: OptSetFailure) ->
            withText `L.isInfixOf` (show e) @?
            ("Expected '" <> withText <> "' exception error but got: " <>
             show e)
          _ -> assertFailure $
               "Expected OptSetFailure exception but got: " <> show err
    wantOptGetFailure withText res = case res of
      Right r ->
        assertFailure ("Expected '" <> withText <>
                       "' but completed successfully with: " <> show r)
      Left err ->
        case fromException err of
          Just (e :: OptGetFailure) ->
            withText `L.isInfixOf` (show e) @?
            ("Expected '" <> withText <> "' exception error but got: " <>
             show e)
          _ -> assertFailure $
               "Expected OptGetFailure exception but got: " <> show err
    withAdapters :: [SolverAdapter EmptyBuilderState]
                 -> (forall t . ExprBuilder t EmptyBuilderState (Flags FloatUninterpreted) -> IO a)
                 -> IO a
    withAdapters adptrs op = do
        (cfgs, _getDefAdapter) <- solverAdapterOptions adptrs
        withIONonceGenerator $ \gen ->
          do sym <- newExprBuilder FloatUninterpretedRepr EmptyBuilderState gen
             extendConfig cfgs (getConfiguration sym)
             op sym

    cmpUnderSomes :: Some OptionSetting -> Some OptionSetting -> IO ()
    cmpUnderSomes (Some setterX) (Some setterY) =
      case testEquality
           (configOptionType (optionSettingName setterX))
           (BaseStringRepr UnicodeRepr) of
        Just Refl ->
          case testEquality
               (configOptionType (optionSettingName setterY))
               (BaseStringRepr UnicodeRepr) of
            Just Refl -> do vX <- getMaybeOpt setterX
                            vY <- getMaybeOpt setterY
                            vX @=? vY
            Nothing -> assertFailure "second some is not a unicode string"
        Nothing -> assertFailure "first some is not a unicode string"

    cmpUnderSomesI :: Some OptionSetting -> Some OptionSetting -> IO ()
    cmpUnderSomesI (Some setterX) (Some setterY) =
      case testEquality BaseIntegerRepr
           (configOptionType (optionSettingName setterX)) of
        Just Refl ->
          case testEquality BaseIntegerRepr
               (configOptionType (optionSettingName setterY)) of
            Just Refl -> do vX <- getMaybeOpt setterX
                            vY <- getMaybeOpt setterY
                            vX @=? vY
            Nothing -> assertFailure "second some is not an integer"
        Nothing -> assertFailure "first some is not an integer"

    cmpUnderSome :: Some OptionSetting
                 -> OptionSetting (BaseStringType Unicode) -> IO ()
    cmpUnderSome (Some setterX) setterY =
      case testEquality
           (configOptionType (optionSettingName setterX))
           (BaseStringRepr UnicodeRepr) of
        Just Refl -> do vX <- getMaybeOpt setterX
                        vY <- getMaybeOpt setterY
                        vX @=? vY
        Nothing -> assertFailure "first some is not a unicode string"

    cmpUnderSomeI :: Some OptionSetting
                 -> OptionSetting BaseIntegerType -> IO ()
    cmpUnderSomeI (Some setterX) setterY =
      case testEquality BaseIntegerRepr
           (configOptionType (optionSettingName setterX)) of
        Just Refl -> do vX <- getMaybeOpt setterX
                        vY <- getMaybeOpt setterY
                        vX @=? vY
        Nothing -> assertFailure "first some is not an integer"

    cmpUnderSomeB :: Some OptionSetting
                 -> OptionSetting BaseBoolType -> IO ()
    cmpUnderSomeB (Some setterX) setterY =
      case testEquality BaseBoolRepr
           (configOptionType (optionSettingName setterX)) of
        Just Refl -> do vX <- getMaybeOpt setterX
                        vY <- getMaybeOpt setterY
                        vX @=? vY
        Nothing -> assertFailure "first some is not a boolean"

    strictParseConfigTests adaptrs =
      let mkPCTest adaptr =
            testGroup (solver_adapter_name adaptr) $
            let setCommonStrictness cfg v = do
                  setter <- getOptionSetting strictSMTParsing cfg
                  show <$> setOpt setter v >>= (@?= "[]")
                setSpecificStrictness cfg v = do
                  setter <- getOptionSettingFromText (pack cfgName) cfg
                  show <$> setBoolOpt setter v >>= (@?= "[]")
                cfgName = "solver." <> (toLower <$> (solver_adapter_name adaptr)) <> ".strict_parsing"
            in [
                 testCase "default val" $
                 withAdapters adaptrs $ \sym -> do
                   let cfg = getConfiguration sym
                       strictOpt = Just $ configOption knownRepr cfgName
                   parserStrictness strictOpt strictSMTParsing cfg >>= (@?= Strict)

               , testCase "common val" $
                 withAdapters adaptrs $ \sym -> do
                   let cfg = getConfiguration sym
                       strictOpt = Just $ configOption knownRepr cfgName
                   setCommonStrictness cfg False
                   parserStrictness strictOpt strictSMTParsing cfg >>= (@?= Lenient)

               , testCase "strict val" $
                 withAdapters adaptrs $ \sym -> do
                   let cfg = getConfiguration sym
                       strictOpt = Just $ configOption knownRepr cfgName
                   setSpecificStrictness cfg False
                   parserStrictness strictOpt strictSMTParsing cfg >>= (@?= Lenient)

               , testCase "strict overrides common val" $
                 withAdapters adaptrs $ \sym -> do
                   let cfg = getConfiguration sym
                       strictOpt = Just $ configOption knownRepr cfgName
                   setCommonStrictness cfg False
                   setSpecificStrictness cfg True
                   parserStrictness strictOpt strictSMTParsing cfg >>= (@?= Strict)

              ]
      in fmap mkPCTest adaptrs

    deprecatedConfigTests adaptrs =
      [

        testCaseSteps "deprecated default_solver is equivalent to solver.default" $
        -- n.b. requires at least 2 entries in the adaptrs list
        \step -> withAdapters adaptrs $ \sym -> do
          step "Get OptionSetters, regular and deprecated, Text and ConfigOption"
          settera <- getOptionSettingFromText "solver.default"
                     (getConfiguration sym)
          setterb <- getOptionSettingFromText "default_solver"
                     (getConfiguration sym)
          settera' <- getOptionSetting defaultSolverAdapter
                     (getConfiguration sym)
          step "Get (same) initial value from regular and deprecated"
          cmpUnderSomes settera setterb
          step "Get (same) initial value from Text and ConfigOption identification"
          cmpUnderSome settera settera'
          v0 <- getMaybeOpt settera'

          step "Update the value via deprecated"
          res1 <- try $ setUnicodeOpt setterb $
                  pack $ solver_adapter_name $ last adaptrs
          case res1 of
            Right warns -> fmap show warns @?=
              [ "DEPRECATED CONFIG OPTION USED: default_solver (renamed to: solver.default)"
              ]
            Left (SomeException e) -> assertFailure $ show e
          -- Get (same) updated value from regular and deprecated
          cmpUnderSomes settera setterb
          v1 <- getMaybeOpt settera'
          (v0 /= v1) @? ("Update from " <> show v0 <> " failed for " <>
                         show (fmap solver_adapter_name adaptrs))

          step "Update the value via regular (text identification)"
          res2 <- try $ setUnicodeOpt settera $
                  pack $ solver_adapter_name $ head adaptrs
          case res2 of
            Right warns -> fmap show warns @?= []
            Left (SomeException e) -> assertFailure $ show e
          v2 <- getMaybeOpt settera'
          v0 @=? v2

          step "Update the value via regular (ConfigOption identification)"
          res3 <- try $ setOpt settera' $
                  pack $ solver_adapter_name $ last $ take 2 adaptrs
          case res3 of
            Right warns -> fmap show warns @?= []
            Left (SomeException e) -> assertFailure $ show e
          v3 <- getMaybeOpt settera'
          (v0 /= v3) @? ("Update from " <> show v0 <> " failed for " <>
                         show (fmap solver_adapter_name adaptrs))

          step "Attempt invalid update via deprecated"
          wantOptSetFailure "invalid setting" =<<
            try (setUnicodeOpt setterb "foo")
          v4 <- getMaybeOpt settera'
          v3 @=? v4

          step "Reset to original value"
          res4 <- try $ setOpt settera' $
                  pack $ solver_adapter_name $ head adaptrs
          case res4 of
            Right warns -> fmap show warns @?= []
            Left (SomeException e) -> assertFailure $ show e
          v5 <- getMaybeOpt settera'
          v0 @=? v5
          cmpUnderSome settera settera'

      , testCase "deprecated boolector_path is equivalent to solver.boolector.path" $
        withAdapters adaptrs $ \sym -> do
          settera <- getOptionSettingFromText "boolector_path"
                     (getConfiguration sym)
          setterb <- getOptionSetting boolectorPath
                     (getConfiguration sym)
          cmpUnderSome settera setterb
          res1 <- try $ setUnicodeOpt settera "/foo/bar"
          case res1 of
            Right warns -> fmap show warns @?=
              [ "Could not find: /foo/bar"
              , "DEPRECATED CONFIG OPTION USED: boolector_path (renamed to: solver.boolector.path)"
              ]
            Left (SomeException e) -> assertFailure $ show e
          cmpUnderSome settera setterb

      , testCase "deprecated cvc4_path is equivalent to solver.cvc4.path" $
        withAdapters adaptrs $ \sym -> do
          settera <- getOptionSettingFromText "cvc4_path"
                     (getConfiguration sym)
          setterb <- getOptionSetting cvc4Path
                     (getConfiguration sym)
          cmpUnderSome settera setterb
          res1 <- try $ setUnicodeOpt settera "/foo/bar"
          case res1 of
            Right warns -> fmap show warns @?=
              [ "Could not find: /foo/bar"
              , "DEPRECATED CONFIG OPTION USED: cvc4_path (renamed to: solver.cvc4.path)"
              ]
            Left (SomeException e) -> assertFailure $ show e
          cmpUnderSome settera setterb

      , testCase "deprecated cvc4_timeout is equivalent to solver.cvc4.timeout" $
        withAdapters adaptrs $ \sym -> do
          settera <- getOptionSettingFromText "cvc4_timeout"
                     (getConfiguration sym)
          setterb <- getOptionSetting cvc4Timeout
                     (getConfiguration sym)
          cmpUnderSomeI settera setterb
          res1 <- try $ setIntegerOpt settera 42
          case res1 of
            Right warns -> fmap show warns @?=
              [ "DEPRECATED CONFIG OPTION USED: cvc4_timeout (renamed to: solver.cvc4.timeout)"
              ]
            Left (SomeException e) -> assertFailure $ show e
          cmpUnderSomeI settera setterb

      , testCase "deprecated stp.random-seed is equivalent to solver.stp.random-seed" $
        withAdapters adaptrs $ \sym -> do
          settera <- getOptionSettingFromText "cvc4.random-seed"
                     (getConfiguration sym)
          setterb <- getOptionSettingFromText "solver.cvc4.random-seed"
                     (getConfiguration sym)
          cmpUnderSomesI settera setterb
          res1 <- try $ setIntegerOpt settera 99
          case res1 of
            Right warns -> fmap show warns @?=
              [ "DEPRECATED CONFIG OPTION USED: cvc4.random-seed (renamed to: solver.cvc4.random-seed)"
              ]
            Left (SomeException e) -> assertFailure $ show e
          cmpUnderSomesI settera setterb

      , (if "dreal" `elem` (solver_adapter_name <$> adapters)
         then id else ignoreTestBecause "dreal not available") $
        testCase "deprecated dreal_path is equivalent to solver.dreal.path" $
        withAdapters adaptrs $ \sym -> do
#ifdef TEST_DREAL
          settera <- getOptionSettingFromText "dreal_path"
                     (getConfiguration sym)
          setterb <- getOptionSetting drealPath
                     (getConfiguration sym)
          cmpUnderSome settera setterb
          res1 <- try $ setUnicodeOpt settera "/foo/bar"
          case res1 of
            Right warns -> fmap show warns @?=
              [ "Could not find: /foo/bar"
              , "DEPRECATED CONFIG OPTION USED: dreal_path (renamed to: solver.dreal.path)"
              ]
            Left (SomeException e) -> assertFailure $ show e
          cmpUnderSome settera setterb
#else
          settera <- try $ getOptionSettingFromText "dreal_path"
                     (getConfiguration sym)
          wantOptGetFailure "not found" settera
#endif

      , (if "abc" `elem` (solver_adapter_name <$> adapters)
         then id else ignoreTestBecause "abc not available") $
        testCase "deprecated abc_path is equivalent to solver.abc.path" $
        withAdapters adaptrs $ \sym -> do
          settera <- getOptionSettingFromText "abc_path"
                     (getConfiguration sym)
          setterb <- getOptionSetting abcPath
                     (getConfiguration sym)
          cmpUnderSome settera setterb
          res1 <- try $ setUnicodeOpt settera "/foo/bar"
          case res1 of
            Right warns -> fmap show warns @?=
              [ "Could not find: /foo/bar"
              , "DEPRECATED CONFIG OPTION USED: abc_path (renamed to: solver.abc.path)"
              ]
            Left (SomeException e) -> assertFailure $ show e
          cmpUnderSome settera setterb

      , (if "stp" `elem` (solver_adapter_name <$> adapters)
         then id else ignoreTestBecause "stp not available") $
        testCase "deprecated stp_path is equivalent to solver.stp.path" $
        withAdapters adaptrs $ \sym -> do
#ifdef TEST_STP
          settera <- getOptionSettingFromText "stp_path"
                     (getConfiguration sym)
          setterb <- getOptionSetting stpPath
                     (getConfiguration sym)
          cmpUnderSome settera setterb
          res1 <- try $ setUnicodeOpt settera "/foo/bar"
          case res1 of
            Right warns -> fmap show warns @?=
              [ "Could not find: /foo/bar"
              , "DEPRECATED CONFIG OPTION USED: stp_path (renamed to: solver.stp.path)"
              ]
            Left (SomeException e) -> assertFailure $ show e
          cmpUnderSome settera setterb
#else
          settera <- try $ getOptionSettingFromText "stp_path"
                     (getConfiguration sym)
          wantOptGetFailure "not found" settera
#endif

      , (if "stp" `elem` (solver_adapter_name <$> adapters)
         then id else ignoreTestBecause "stp not available") $
        testCase "deprecated stp.random-seed is equivalent to solver.stp.random-seed" $
        withAdapters adaptrs $ \sym -> do
#ifdef TEST_STP
          settera <- getOptionSettingFromText "stp.random-seed"
                     (getConfiguration sym)
          setterb <- getOptionSettingFromText "solver.stp.random-seed"
                     (getConfiguration sym)
          cmpUnderSomesI settera setterb
          res1 <- try $ setIntegerOpt settera 99
          case res1 of
            Right warns -> fmap show warns @?=
              [ "DEPRECATED CONFIG OPTION USED: stp.random-seed (renamed to: solver.stp.random-seed)"
              ]
            Left (SomeException e) -> assertFailure $ show e
          cmpUnderSomesI settera setterb
#else
          settera <- try $ getOptionSettingFromText "stp.random-seed"
                     (getConfiguration sym)
          wantOptGetFailure "not found" settera
#endif

      , testCase "deprecated yices_path is equivalent to solver.yices.path" $
        withAdapters adaptrs $ \sym -> do
          settera <- getOptionSettingFromText "yices_path"
                     (getConfiguration sym)
          setterb <- getOptionSetting yicesPath
                     (getConfiguration sym)
          cmpUnderSome settera setterb
          res1 <- try $ setUnicodeOpt settera "/foo/bar"
          case res1 of
            Right warns -> fmap show warns @?=
              [ "Could not find: /foo/bar"
              , "DEPRECATED CONFIG OPTION USED: yices_path (renamed to: solver.yices.path)"
              ]
            Left (SomeException e) -> assertFailure $ show e
          cmpUnderSome settera setterb

      , testCase "deprecated yices_enable-interactive is equivalent to solver.yices.en.." $
        withAdapters adaptrs $ \sym -> do
          settera <- getOptionSettingFromText "yices_enable-interactive"
                     (getConfiguration sym)
          setterb <- getOptionSetting yicesEnableInteractive
                     (getConfiguration sym)
          cmpUnderSomeB settera setterb
          res1 <- try $ setBoolOpt settera True
          case res1 of
            Right warns -> fmap show warns @?=
              [ "DEPRECATED CONFIG OPTION USED: yices_enable-interactive (renamed to: solver.yices.enable-interactive)"
              ]
            Left (SomeException e) -> assertFailure $ show e
          cmpUnderSomeB settera setterb

      , testCase "deprecated yices_enable-mcsat is equivalent to solver.yices.enable-mcsat" $
        withAdapters adaptrs $ \sym -> do
          settera <- getOptionSettingFromText "yices_enable-mcsat"
                     (getConfiguration sym)
          setterb <- getOptionSetting yicesEnableMCSat
                     (getConfiguration sym)
          cmpUnderSomeB settera setterb
          res1 <- try $ setBoolOpt settera True
          case res1 of
            Right warns -> fmap show warns @?=
              [ "DEPRECATED CONFIG OPTION USED: yices_enable-mcsat (renamed to: solver.yices.enable-mcsat)"
              ]
            Left (SomeException e) -> assertFailure $ show e
          cmpUnderSomeB settera setterb

      , testCase "deprecated yices_goal-timeout is equivalent to solver.yices.goal-timeout" $
        withAdapters adaptrs $ \sym -> do
          settera <- getOptionSettingFromText "yices_goal-timeout"
                     (getConfiguration sym)
          setterb <- getOptionSetting yicesGoalTimeout
                     (getConfiguration sym)
          cmpUnderSomeI settera setterb
          res1 <- try $ setIntegerOpt settera 123
          case res1 of
            Right warns -> fmap show warns @?=
              [ "DEPRECATED CONFIG OPTION USED: yices_goal-timeout (renamed to: solver.yices.goal-timeout)"
              ]
            Left (SomeException e) -> assertFailure $ show e
          cmpUnderSomeI settera setterb

      , testCase "deprecated z3_path is equivalent to solver.z3.path" $
        withAdapters adaptrs $ \sym -> do
          settera <- getOptionSettingFromText "z3_path"
                     (getConfiguration sym)
          setterb <- getOptionSetting z3Path
                     (getConfiguration sym)
          cmpUnderSome settera setterb
          res1 <- try $ setUnicodeOpt settera "/bar/foo"
          case res1 of
            Right warns -> fmap show warns @?=
              [ "Could not find: /bar/foo"
              , "DEPRECATED CONFIG OPTION USED: z3_path (renamed to: solver.z3.path)"
              ]
            Left (SomeException e) -> assertFailure $ show e
          cmpUnderSome settera setterb

      , testCase "deprecated z3_timeout is equivalent to solver.z3.timeout" $
        withAdapters adaptrs $ \sym -> do
          settera <- getOptionSettingFromText "z3_timeout"
                     (getConfiguration sym)
          setterb <- getOptionSetting z3Timeout
                     (getConfiguration sym)
          cmpUnderSomeI settera setterb
          res1 <- try $ setIntegerOpt settera 123
          case res1 of
            Right warns -> fmap show warns @?=
              [ "DEPRECATED CONFIG OPTION USED: z3_timeout (renamed to: solver.z3.timeout)"
              ]
            Left (SomeException e) -> assertFailure $ show e
          cmpUnderSomeI settera setterb

      ]


----------------------------------------------------------------------

nonlinearRealTest :: SolverAdapter EmptyBuilderState -> TestTree
nonlinearRealTest adpt =
  let wrap = if solver_adapter_name adpt `elem` [ "ABC", "boolector", "stp" ]
             then expectFailBecause
                  (solver_adapter_name adpt
                   <> " does not support this type of linear arithmetic term")
             else id
  in wrap $ testCase (solver_adapter_name adpt) $
  withSym adpt $ \sym ->
    do x <- freshConstant sym (safeSymbol "a") BaseRealRepr
       y <- freshConstant sym (safeSymbol "b") BaseRealRepr

       xabs <- realAbs sym x

       x2 <- realMul sym x x

       x2_1 <- realAdd sym x2 =<< realLit sym 1
       x2_y <- realAdd sym x2 y

       p1 <- realLt sym x2_1 =<< realLit sym 0

       p2 <- realLe sym x2_y =<< realLit sym (-1)
       p3 <- realGe sym x2_y =<< realLit sym (-2)
       p4 <- realLe sym xabs =<< realLit sym 10

       -- asking if `x^2 < 0` should be unsat
       solver_adapter_check_sat adpt sym defaultLogData [p1] $ \case
           Unsat _ -> return ()
           Unknown -> fail "Solver returned UNKNOWN"
           Sat _ -> fail "Should be UNSAT!"

       -- asking to find `-2 <= x^2 + y <= -1` with `abs(x) <= 10`. Should find something.
       solver_adapter_check_sat adpt sym defaultLogData [p2,p3,p4] $ \case
           Unsat _ -> fail "Shoule be UNSAT!"
           Unknown -> fail "Solver returned UNKNOWN"
           Sat (eval,_bounds) ->
             do x' <- groundEval eval x
                abs x' <= 10 @? "correct abs(x) bound"

                x2_y' <- groundEval eval x2_y
                ((-2) <= x2_y' && x2_y' <= (-1)) @? "correct bounds"


mkQuickstartTest :: SolverAdapter EmptyBuilderState -> TestTree
mkQuickstartTest adpt =
  let wrap = if solver_adapter_name adpt == "stp"
             then ignoreTestBecause "STP cannot generate the model"
             else id
  in wrap $
  testCase (solver_adapter_name adpt) $
  withSym adpt $ \sym ->
    do -- Let's determine if the following formula is satisfiable:
       -- f(p, q, r) = (p | !q) & (q | r) & (!p | !r) & (!p | !q | r)

       -- First, declare fresh constants for each of the three variables p, q, r.
       p <- freshConstant sym (safeSymbol "p") BaseBoolRepr
       q <- freshConstant sym (safeSymbol "q") BaseBoolRepr
       r <- freshConstant sym (safeSymbol "r") BaseBoolRepr

       -- Next, create terms for the negation of p, q, and r.
       not_p <- notPred sym p
       not_q <- notPred sym q
       not_r <- notPred sym r

       -- Next, build up each clause of f individually.
       clause1 <- orPred sym p not_q
       clause2 <- orPred sym q r
       clause3 <- orPred sym not_p not_r
       clause4 <- orPred sym not_p =<< orPred sym not_q r

       -- Finally, create f out of the conjunction of all four clauses.
       f <- andPred sym clause1 =<<
            andPred sym clause2 =<<
            andPred sym clause3 clause4

       (p',q',r') <-
         solver_adapter_check_sat adpt sym defaultLogData [f] $ \case
           Unsat _ -> fail "Unsatisfiable"
           Unknown -> fail "Solver returned UNKNOWN"
           Sat (eval, _) ->
               do p' <- groundEval eval p
                  q' <- groundEval eval q
                  r' <- groundEval eval r
                  return (p',q',r')

       -- This is the unique satisfiable model
       p' == False @? "p value"
       q' == False @? "q value"
       r' == True  @? "r value"

       -- Compute a blocking predicate for the computed model
       bs <- forM [(p,p'),(q,q'),(r,r')] $ \(x,v) -> eqPred sym x (backendPred sym v)
       block <- notPred sym =<< andAllOf sym folded bs

       -- Ask if there is some other model
       solver_adapter_check_sat adpt sym defaultLogData [f,block] $ \case
           Unsat _ -> return ()
           Unknown -> fail "Solver returned UNKNOWN"
           Sat _   -> fail "Should be a unique model!"

verilogTest :: TestTree
verilogTest = testCase "verilogTest" $ withIONonceGenerator $ \gen ->
  do sym <- newExprBuilder FloatUninterpretedRepr EmptyBuilderState gen
     let w = knownNat @8
     x <- freshConstant sym (safeSymbol "x") (BaseBVRepr w)
     one <- bvLit sym w (mkBV w 1)
     add <- bvAdd sym x one
     r <- notPred sym =<< bvEq sym x add
     edoc <- runExceptT (exprsVerilog sym [] [Some r] "f")
     case edoc of
       Left err -> fail $ "Failed to translate to Verilog: " ++ err
       Right doc ->
         unless (show doc ++ "\n" == refDoc) $
           fail $ unlines [
                     "Unexpected output from Verilog translation:"
                    , show doc
                    , "instead of"
                    , refDoc
                    ]
  where
    refDoc = unlines [ "module f(x, out);"
                     , "  input [7:0] x;"
                     , "  wire [7:0] wr = 8'h1;"
                     , "  wire [7:0] wr_2 = wr * x;"
                     , "  wire [7:0] wr_3 = wr + wr_2;"
                     , "  wire wr_4 = wr_3 == x;"
                     , "  wire wr_5 = ! wr_4;"
                     , "  output out = wr_5;"
                     , "endmodule"
                     ]

main :: IO ()
main = do
  testLevel <- TestLevel . fromMaybe "0" <$> lookupEnv "CI_TEST_LEVEL"
  let solverNames = SolverName . solver_adapter_name <$> allAdapters
  solvers <- reportSolverVersions testLevel (SolverName . solver_adapter_name)
             =<< (zip allAdapters <$> mapM getSolverVersion solverNames)
  let adapters = fst <$> solvers
  defaultMain $
    localOption (mkTimeout (10 * 1000 * 1000)) $
    testGroup "AdapterTests"
    [ testGroup "SmokeTest" $ map mkSmokeTest adapters
    , testGroup "Config Tests" $ mkConfigTests adapters
    , testGroup "QuickStart" $ map mkQuickstartTest adapters
    , testGroup "nonlinear reals" $ map nonlinearRealTest adapters
    , testGroup "Verilog" [verilogTest]
    ]

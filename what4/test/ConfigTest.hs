{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

import           Control.Exception ( displayException, try, SomeException(..), fromException )
import qualified Data.List as L
import           Data.Parameterized.Context ( pattern Empty, pattern (:>) )
import           Data.Parameterized.Some
import           Data.Ratio ( (%) )
import qualified Data.Set as Set
import qualified Data.Text as T
import           Data.Void
import qualified Prettyprinter as PP

import           Test.Tasty
import           Test.Tasty.Checklist
import           Test.Tasty.HUnit

import           What4.BaseTypes
import           What4.Concrete
import           What4.Config


testSetAndGet :: [TestTree]
testSetAndGet =
  [
    testCase "create multiple options" $ do
      cfg <- initialConfig 0 []
      let o1 = configOption (BaseStringRepr UnicodeRepr) "optstr"
          o2 = configOption BaseIntegerRepr "optint"
          o3 = configOption BaseBoolRepr "optbool"
          o1' = mkOpt o1 stringOptSty Nothing Nothing
          o2' = mkOpt o2 integerOptSty Nothing Nothing
          o3' = mkOpt o3 boolOptSty Nothing Nothing
      extendConfig [o3', o2', o1'] cfg

  , testCase "create conflicting options" $ do
      cfg <- initialConfig 0 []
      let o1 = configOption (BaseStringRepr UnicodeRepr) "mainopt"
          o2 = configOption BaseIntegerRepr "mainopt"
          o1' = mkOpt o1 stringOptSty Nothing Nothing
          o2' = mkOpt o2 integerOptSty Nothing Nothing
      res <- try $ extendConfig [o2', o1'] cfg
      wantOptCreateFailure "already exists with type" res

  , testCase "create conflicting options at different levels" $ do
      cfg <- initialConfig 0 []
      let o1 = configOption (BaseStringRepr UnicodeRepr) "mainopt"
          o2 = configOption BaseIntegerRepr "main.mainopt"
          o1' = mkOpt o1 stringOptSty Nothing Nothing
          o2' = mkOpt o2 integerOptSty Nothing Nothing
      res <- try @SomeException $ extendConfig [o2', o1'] cfg
      case res of
        Right () -> return ()
        Left e -> assertFailure $ "Unexpected exception: " <> displayException e

  , testCase "create duplicate unicode options" $ do
      cfg <- initialConfig 0 []
      let o1 = configOption (BaseStringRepr UnicodeRepr) "mainopt"
          o2 = configOption (BaseStringRepr UnicodeRepr) "mainopt"
          o1' = mkOpt o1 stringOptSty Nothing Nothing
          o2' = mkOpt o2 stringOptSty Nothing Nothing
      res <- try @SomeException $ extendConfig [o2', o1'] cfg
      case res of
        Right () -> return ()
        Left e -> assertFailure $ "Unexpected exception: " <> displayException e

  , testCaseSteps "get unset value, no default" $ \step -> do
      cfg <- initialConfig 0 []
      let o1 = configOption (BaseStringRepr UnicodeRepr) "optstr"
          o2 = configOption BaseIntegerRepr "optint"
          o3 = configOption BaseBoolRepr "optbool"
          o1' = mkOpt o1 stringOptSty Nothing Nothing
          o2' = mkOpt o2 integerOptSty Nothing Nothing
          o3' = mkOpt o3 boolOptSty Nothing Nothing
      extendConfig [o3', o2', o1'] cfg
      access1 <- getOptionSetting o1 cfg
      access2 <- getOptionSetting o2 cfg
      access3 <- getOptionSetting o3 cfg

      step "get unset string opt"
      v1 <- getMaybeOpt access1
      Nothing @=? v1
      res1 <- try $ getOpt access1
      wantOptGetFailure "not set" res1

      step "get unset integer opt"
      v2 <- getMaybeOpt access2
      Nothing @=? v2
      res2 <- try $ getOpt access2
      wantOptGetFailure "not set" res2

      step "get unset bool opt"
      v3 <- getMaybeOpt access3
      Nothing @=? v3
      res3 <- try $ getOpt access3
      wantOptGetFailure "not set" res3

  , testCaseSteps "get unset value, with default" $ \step -> do
      cfg <- initialConfig 0 []
      let o1 = configOption (BaseStringRepr UnicodeRepr) "optstr"
          o2 = configOption BaseIntegerRepr "optint"
          o3 = configOption BaseBoolRepr "optbool"
          o1' = mkOpt o1 stringOptSty Nothing (Just $ ConcreteString "strval")
          o2' = mkOpt o2 integerOptSty Nothing (Just $ ConcreteInteger 11)
          o3' = mkOpt o3 boolOptSty Nothing (Just $ ConcreteBool True)
      extendConfig [o3', o2', o1'] cfg
      access1 <- getOptionSetting o1 cfg
      access2 <- getOptionSetting o2 cfg
      access3 <- getOptionSetting o3 cfg
      step "get unset default string opt"
      v1 <- getMaybeOpt access1
      Just "strval" @=? v1
      step "get unset default integer opt"
      v2 <- getMaybeOpt access2
      Just 11 @=? v2
      step "get unset default bool opt"
      v3 <- getMaybeOpt access3
      Just True @=? v3

  , testCaseSteps "get set value, with default" $ \step -> do
      cfg <- initialConfig 0 []
      let o1 = configOption (BaseStringRepr UnicodeRepr) "optstr"
          o2 = configOption BaseIntegerRepr "optint"
          o3 = configOption BaseBoolRepr "optbool"
          o1' = mkOpt o1 stringOptSty Nothing (Just $ ConcreteString "strval")
          o2' = mkOpt o2 integerOptSty Nothing (Just $ ConcreteInteger 11)
          o3' = mkOpt o3 boolOptSty Nothing (Just $ ConcreteBool True)
      extendConfig [o3', o2', o1'] cfg
      access1 <- getOptionSetting o1 cfg
      access2 <- getOptionSetting o2 cfg
      access3 <- getOptionSetting o3 cfg

      step "set string opt"
      res1 <- setOpt access1 "flibberty"
      show <$> res1 @?= []

      step "set bool opt"
      res2 <- setOpt access3 False
      show <$> res2 @?= []

      step "set integer opt"
      res3 <- setOpt access2 9945
      show <$> res3 @?= []

      step "get string opt"
      v1 <- getMaybeOpt access1
      Just "flibberty" @=? v1
      step "get integer opt"
      v2 <- getMaybeOpt access2
      Just 9945 @=? v2
      step "get bool opt"
      v3 <- getMaybeOpt access3
      Just False @=? v3

  , testCaseSteps "set invalid values" $ \step -> do
      cfg <- initialConfig 0 []
      let o1 = configOption (BaseStringRepr UnicodeRepr) "optstr"
          o2 = configOption BaseIntegerRepr "optint"
          o3 = configOption BaseRealRepr "optbool"
          -- n.b. the default values are not checked by the style!
          o1' = mkOpt o1 (enumOptSty
                          (Set.fromList ["eeny", "meeny", "miny", "mo" ]))
                Nothing (Just $ ConcreteString "strval")
          o2' = mkOpt o2 (integerWithRangeOptSty Unbounded (Inclusive 10))
                Nothing (Just $ ConcreteInteger 11)
          o3' = mkOpt o3 (realWithMinOptSty (Exclusive 1.23))
                Nothing (Just $ ConcreteReal 0.0)
      extendConfig [o3', o2', o1'] cfg
      access1 <- getOptionSetting o1 cfg
      access2 <- getOptionSetting o2 cfg
      access3 <- getOptionSetting o3 cfg

      step "initial defaults"
      getMaybeOpt access1 >>= (@?= Just "strval")
      getMaybeOpt access2 >>= (@?= Just 11)
      getMaybeOpt access3 >>= (@?= Just (0 % 1 :: Rational))

      step "set string opt invalidly"
      -- Note: the strong typing prevents both of the following
      -- setOpt access1 32
      -- setOpt access1 False
      res1 <- try $ setOpt access1 "frobozz"
      wantOptSetFailure "invalid setting \"frobozz\"" res1
      wantOptSetFailure "eeny, meeny, miny, mo" res1
      (try @SomeException $ setOpt access1 "meeny") >>= \case
        Right [] -> return ()
        Right w -> assertFailure $ "Unexpected warnings: " <> show w
        Left e -> assertFailure $ "Unexpected exception: " <> displayException e

      step "set integer opt invalidly"
      wantOptSetFailure "out of range" =<< (try $ setOpt access2 11)
      wantOptSetFailure "expected integer value in (-∞, 10]" =<< (try $ setOpt access2 11)
      (try @SomeException $ setOpt access2 10) >>= \case
        Right [] -> return ()
        Right w -> assertFailure $ "Unexpected warnings: " <> show w
        Left e -> assertFailure $ "Unexpected exception: " <> displayException e
      (try @SomeException $ setOpt access2 (-3)) >>= \case
        Right [] -> return ()
        Right w -> assertFailure $ "Unexpected warnings: " <> show w
        Left e -> assertFailure $ "Unexpected exception: " <> displayException e

      step "set real opt invalidly"
      wantOptSetFailure "out of range" =<< (try $ setOpt access3 (0 % 3))
      wantOptSetFailure "expected real value in (123 % 100, +∞)"
        =<< (try $ setOpt access3 (0 % 3))
      wantOptSetFailure "out of range" =<< (try $ setOpt access3 (1229 % 1000))
      wantOptSetFailure "out of range" =<< (try $ setOpt access3 (123 % 100))
      (try @SomeException $ setOpt access3 (123001 % 100000)) >>= \case
        Right [] -> return ()
        Right w -> assertFailure $ "Unexpected warnings: " <> show w
        Left e -> assertFailure $ "Unexpected exception: " <> displayException e

  , testCaseSteps "get and set option values by name" $ \step ->
      withChecklist "multiple values" $ do
      cfg <- initialConfig 0 []
      let o1 = configOption (BaseStringRepr UnicodeRepr) "main.optstr"
          o2 = configOption BaseIntegerRepr "main.set.cfg.optint"
          o3 = configOption BaseBoolRepr "main.set.cfg.optbool"
          o4 = configOption BaseIntegerRepr "alt.optint"
          o1' = mkOpt o1 stringOptSty Nothing (Just $ ConcreteString "strval")
          o2' = mkOpt o2 integerOptSty Nothing (Just $ ConcreteInteger 11)
          o3' = mkOpt o3 boolOptSty Nothing (Just $ ConcreteBool True)
          o4' = mkOpt o4 integerOptSty Nothing (Just $ ConcreteInteger 88)
      extendConfig [o4', o3', o2', o1'] cfg
      accessSome1 <- getOptionSettingFromText "main.optstr" cfg
      accessSome2 <- getOptionSettingFromText "main.set.cfg.optint" cfg
      accessSome3 <- getOptionSettingFromText "main.set.cfg.optbool" cfg
      accessSome4 <- getOptionSettingFromText "alt.optint" cfg

      access1 <- getOptionSetting o1 cfg
      access2 <- getOptionSetting o2 cfg
      access3 <- getOptionSetting o3 cfg
      access4 <- getOptionSetting o4 cfg

      step "getting with a Some OptionSetter requires type verification"
      let cmpUnderSome :: Some OptionSetting -> T.Text -> IO ()
          cmpUnderSome (Some getter) v =
            case testEquality
                 (configOptionType (optionSettingName getter))
                 (BaseStringRepr UnicodeRepr) of
              Just Refl -> do vt <- getMaybeOpt getter
                              Just v @=? vt
              Nothing -> assertFailure "invalid option type"
      cmpUnderSome accessSome1 "strval"

      step "setting using special setting functions"
      let goodNoWarn f s v =
            (try @SomeException $ f s v) >>= \case
            Right [] -> return ()
            Right w -> assertFailure $ "Unexpected warnings: " <> show w
            Left e -> assertFailure $ "Unexpected exception: " <> displayException e
      goodNoWarn setUnicodeOpt accessSome1 "wild carrots"
      goodNoWarn setIntegerOpt accessSome2 31
      goodNoWarn setIntegerOpt accessSome4 42
      goodNoWarn setBoolOpt accessSome3 False

      step "verify set values"
      (Just "wild carrots" @=?) =<< getMaybeOpt access1
      (Just 31 @=?) =<< getMaybeOpt access2
      (Just False @=?) =<< getMaybeOpt access3
      (Just 42 @=?) =<< getMaybeOpt access4

      step "cannot set values with wrong types"
      -- Note that using an OptionSetting allows compile-time
      -- elimination, but using a (Some OptionSetting) requires
      -- run-time type witnessing and validation
      wantOptSetFailure "type is a BaseStringRepr"
        =<< (try $ setIntegerOpt accessSome1 54)
      wantOptSetFailure "but given an integer"
        =<< (try $ setIntegerOpt accessSome1 54)

      wantOptSetFailure "type is a BaseStringRepr"
        =<< (try $ setBoolOpt accessSome1 True)
      wantOptSetFailure "but given a boolean"
        =<< (try $ setBoolOpt accessSome1 True)

      wantOptSetFailure "type is a BaseIntegerRepr"
        =<< (try $ setUnicodeOpt accessSome2 "fresh tomatoes")
      wantOptSetFailure "but given a text string"
        =<< (try $ setUnicodeOpt accessSome2 "fresh tomatoes")


  , testCaseSteps "get multiple values at once" $ \step ->
      withChecklist "multiple values" $ do
      cfg <- initialConfig 0 []
      let o1 = configOption (BaseStringRepr UnicodeRepr) "main.optstr"
          o2 = configOption BaseIntegerRepr "main.set.cfg.optint"
          o3 = configOption BaseBoolRepr "main.set.cfg.optbool"
          o4 = configOption BaseIntegerRepr "alt.optint"
          o1' = mkOpt o1 stringOptSty Nothing (Just $ ConcreteString "strval")
          o2' = mkOpt o2 integerOptSty Nothing (Just $ ConcreteInteger 11)
          o3' = mkOpt o3 boolOptSty Nothing (Just $ ConcreteBool True)
          o4' = mkOpt o4 integerOptSty Nothing (Just $ ConcreteInteger 88)
      extendConfig [o4', o3', o2', o1'] cfg
      access1 <- getOptionSetting o1 cfg
      access3 <- getOptionSetting o3 cfg
      access4 <- getOptionSetting o4 cfg

      step "set string opt"
      res1 <- setOpt access1 "flibberty"
      show <$> res1 @?= []

      step "set bool opt"
      res2 <- setOpt access3 False
      show <$> res2 @?= []

      step "set alt int opt"
      res4 <- setOpt access4 789
      show <$> res4 @?= []

      step "get main config values"
      res <- getConfigValues "main.set" cfg
      let msg = show . PP.pretty <$> res
      msg `checkValues`
        (Empty
        :> Val "num values" length 2
        :> Val "bool" (any (L.isInfixOf "main.set.cfg.optbool = False")) True
        :> Val "int" (any (L.isInfixOf "main.set.cfg.optint = 11")) True
        )

      step "get all config values"
      resAll <- getConfigValues "" cfg
      let msgAll = show . PP.pretty <$> resAll
      msgAll `checkValues`
        (Empty
        :> Val "num values" length 5
        :> Val "bool" (any (L.isInfixOf "main.set.cfg.optbool = False")) True
        :> Val "int" (any (L.isInfixOf "main.set.cfg.optint = 11")) True
        :> Val "alt int" (any (L.isInfixOf "alt.optint = 789")) True
        :> Val "str" (any (L.isInfixOf "main.optstr = \"flibberty\"")) True
        :> Val "verbosity" (any (L.isInfixOf "verbosity = 0")) True
        )

      step "get specific config value"
      resOne <- getConfigValues "alt.optint" cfg
      let msgOne = show . PP.pretty <$> resOne
      msgOne `checkValues`
        (Empty
        :> Val "num values" length 1
        :> Val "alt int" (any (L.isInfixOf "alt.optint = 789")) True
        )

      step "get unknown config value"
      resNope <- getConfigValues "fargle.bargle" cfg
      let msgNope = show . PP.pretty <$> resNope
      msgNope `checkValues` (Empty :> Val "num values" length 0)


  ]

testDeprecated :: [TestTree]
testDeprecated =
  [
    testCase "deprecation removal (case #1)" $ do
      cfg <- initialConfig 0 []
      let o1 = configOption (BaseStringRepr UnicodeRepr) "hello"
          o1' = mkOpt o1 stringOptSty (Just "greeting") Nothing
      extendConfig [deprecatedOpt [] o1'] cfg
      setter <- getOptionSetting o1 cfg
      res <- try $ setOpt setter "eh?"
      case res of
        Right warns ->
          fmap show warns @?=
          [ "DEPRECATED CONFIG OPTION WILL BE IGNORED: hello (no longer valid)"
          ]
        Left (SomeException e) -> assertFailure $ show e

  , testCase "deprecation rename (case #2)" $ do
      cfg <- initialConfig 0 []
      let o1 = configOption (BaseStringRepr UnicodeRepr) "hi"
          o2 = configOption (BaseStringRepr UnicodeRepr) "hello"
          o1' = deprecatedOpt [o2'] $
                mkOpt o1 stringOptSty (Just "greeting") Nothing
          o2' = mkOpt o2 stringOptSty (Just "greeting") Nothing
      extendConfig [o2', o1'] cfg
      setter <- getOptionSetting o1 cfg
      res <- try $ setOpt setter "eh?"
      case res of
        Right warns ->
          fmap show warns @?=
          [ "DEPRECATED CONFIG OPTION USED: hi (renamed to: hello)"
          ]
        Left (SomeException e) -> assertFailure $ show e

  , testCase "deprecation rename (case #2), wrong order" $ do
      cfg <- initialConfig 0 []
      let o1 = configOption (BaseStringRepr UnicodeRepr) "yo"
          o2 = configOption (BaseStringRepr UnicodeRepr) "hello"
          o1' = deprecatedOpt [o2'] $
                mkOpt o1 stringOptSty (Just "greeting") Nothing
          o2' = mkOpt o2 stringOptSty (Just "greeting") Nothing
      res <- try $ extendConfig [o1', o2'] cfg
      wantOptCreateFailure
        "replacement options must be inserted into Config \
        \before this deprecated option"
        res

  , testCase "deprecation rename and re-typed (case #3)" $ do
      cfg <- initialConfig 0 []
      let o1 = configOption (BaseStringRepr UnicodeRepr) "optstr"
          o2 = configOption BaseIntegerRepr "optnum"
          o1' = deprecatedOpt [o2'] $
                mkOpt o1 stringOptSty (Just "some opt") Nothing
          o2' = mkOpt o2 integerOptSty (Just "some other opt") Nothing
      extendConfig [o2', o1'] cfg
      setter <- getOptionSetting o1 cfg
      res <- try $ setOpt setter "eh?"
      case res of
        Right warns ->
          fmap show warns @?=
          [ "DEPRECATED CONFIG OPTION USED: optstr::BaseStringRepr UnicodeRepr (changed to: \"optnum\"::BaseIntegerRepr); this value may be ignored"
          ]
        Left (SomeException e) -> assertFailure $ show e

  , testCase "deprecation, multiple replacements (case #4)" $ do
      cfg <- initialConfig 0 []
      let o1 = configOption (BaseStringRepr UnicodeRepr) "url"
          o2 = configOption (BaseStringRepr UnicodeRepr) "hostname"
          o3 = configOption BaseIntegerRepr "port"
          o1' = deprecatedOpt [o2', o3'] $
                mkOpt o1 stringOptSty (Just "some opt") Nothing
          o2' = mkOpt o2 stringOptSty (Just "some other opt") Nothing
          o3' = mkOpt o3 integerOptSty (Just "some other opt") Nothing
      extendConfig [o3', o2', o1'] cfg
      setter <- getOptionSetting o1 cfg
      res <- try $ setOpt setter "here?"
      case res of
        Right warns ->
          fmap show warns @?=
          [ "DEPRECATED CONFIG OPTION USED: url::BaseStringRepr UnicodeRepr (replaced by: \"hostname\"::BaseStringRepr UnicodeRepr, \"port\"::BaseIntegerRepr); this value may be ignored"
          ]
        Left (SomeException e) -> assertFailure $ show e

  , testCase "deprecation, multiple + removed/split (case #4,(#1,#3))" $ do
      cfg <- initialConfig 0 []
      let o1 = configOption (BaseStringRepr UnicodeRepr) "url"
          o2 = configOption (BaseStringRepr UnicodeRepr) "hostname"
          o3 = configOption BaseIntegerRepr "port"
          o4 = configOption (BaseStringRepr UnicodeRepr) "host"
          o5 = configOption (BaseStringRepr UnicodeRepr) "domain"
          o1' = deprecatedOpt [o2', o3'] $
                mkOpt o1 stringOptSty (Just "some opt") Nothing
          o2' = deprecatedOpt [o4', o5'] $
                mkOpt o2 stringOptSty (Just "some other opt") Nothing
          o3' = deprecatedOpt [] $
                mkOpt o3 integerOptSty (Just "some other opt") Nothing
          o4' = mkOpt o4 stringOptSty (Nothing) Nothing
          o5' = mkOpt o5 stringOptSty (Just "some opt") (Just $ ConcreteString "cow.barn")
      extendConfig [ o4', o5', o2', o3', o1' ] cfg
      setter <- getOptionSetting o1 cfg
      res <- try $ setOpt setter "here?"
      case res of
        Right warns ->
          fmap show warns @?=
          [ "DEPRECATED CONFIG OPTION USED: url::BaseStringRepr UnicodeRepr (replaced by: \"host\"::BaseStringRepr UnicodeRepr, \"domain\"::BaseStringRepr UnicodeRepr); this value may be ignored"
          ]
        Left (SomeException e) -> assertFailure $ show e

  ]

testHelp :: [TestTree]
testHelp =
  [
    testCase "builtin-only config help" $
    withChecklist "builtins" $ do
      cfg <- initialConfig 0 []
      help <- configHelp "" cfg
      help `checkValues`
        (Empty
        :> Val "num" length 1
        :> Val "verbosity" (L.isInfixOf "verbosity =" . show . head) True
        )


  , testCaseSteps "three item (1 deprecated) config help" $ \step ->
      withChecklist "three items" $ do
      cfg <- initialConfig 0 []
      let o1 = configOption (BaseStringRepr UnicodeRepr) "optstr"
          o2 = configOption BaseIntegerRepr "optnum"
          o3 = configOption BaseIntegerRepr "foo.bar.baz.num"
          o1' = mkOpt o1 stringOptSty (Just "some opt") Nothing
          o2' = mkOpt o2 integerOptSty (Just "some other opt") Nothing
          o3' = mkOpt o3 integerOptSty (Just "foo stuff") Nothing
          helpIncludes txts = any (\h -> all (\t -> L.isInfixOf t (show h)) txts)
      extendConfig [o2', deprecatedOpt [o2'] o1', o3'] cfg
      setter2 <- getOptionSetting o2 cfg
      setRes <- setOpt setter2 13
      setRes `checkValues` (Empty :> Val "no warnings" null True)

      step "all help"
      help <- configHelp "" cfg
      help `checkValues`
        (Empty
        :> Val "num" length 4
        :> Val "verbosity" (helpIncludes ["verbosity ="]) True
        :> Val "option 1" (helpIncludes ["optstr"
                                        , "some opt"
                                        , "DEPRECATED!"
                                        , "Suggest"
                                        , "to \"optnum\""
                                        ]) True
        :> Val "option 2" (helpIncludes ["optnum", "= 13", "some other opt"]) True
        :> Val "option 3" (helpIncludes ["foo.bar.baz.num", "foo stuff"]) True
        )

      step "sub help"
      subHelp <- configHelp "foo.bar" cfg
      subHelp `checkValues`
        (Empty
        :> Val "num" length 1
        :> Val "option 3" (helpIncludes ["foo.bar.baz.num", "foo stuff"]) True
        )

      step "specific help"
      spec <- configHelp "optstr" cfg
      spec `checkValues`
        (Empty
        :> Val "num" length 1
        :> Val "spec name" (helpIncludes ["optstr"]) True
        :> Val "spec opt help" (helpIncludes ["some opt"]) True
        :> Val "spec opt help deprecated" (helpIncludes [ "DEPRECATED!"
                                                        , "Suggest"
                                                        , "to \"optnum\""
                                                        ]) True
        )

      step "specific sub help"
      subspec <- configHelp "foo.bar.baz.num" cfg
      subspec `checkValues`
        (Empty
        :> Val "num" length 1
        :> Val "option 3" (helpIncludes ["foo.bar.baz.num", "foo stuff"]) True
        )

  ]

instance TestShow (PP.Doc Void) where testShow = show
instance TestShow [PP.Doc Void] where testShow = testShowList
instance TestShow [String] where testShow = testShowList

wantOptCreateFailure :: Show a => String -> Either SomeException a -> IO ()
wantOptCreateFailure withText res = case res of
  Right r ->
    assertFailure ("Expected '" <> withText <>
                   "' but completed successfully with: " <> show r)
  Left err ->
    case fromException err of
      Just (e :: OptCreateFailure) ->
        withText `L.isInfixOf` (show e) @?
        ("Expected '" <> withText <> "' exception error but got: " <>
         displayException e)
      _ -> assertFailure $
           "Expected OptCreateFailure exception but got: " <>
           displayException err

wantOptSetFailure :: Show a => String -> Either SomeException a -> IO ()
wantOptSetFailure withText res = case res of
  Right r ->
    assertFailure ("Expected '" <> withText <>
                   "' but completed successfully with: " <> show r)
  Left err ->
    case fromException err of
      Just (e :: OptSetFailure) ->
        withText `L.isInfixOf` (show e) @?
        ("Expected '" <> withText <> "' exception error but got: " <>
         displayException e)
      _ -> assertFailure $
           "Expected OptSetFailure exception but got: " <>
           displayException err

wantOptGetFailure :: Show a => String -> Either SomeException a -> IO ()
wantOptGetFailure withText res = case res of
  Right r ->
    assertFailure ("Expected '" <> withText <>
                   "' but completed successfully with: " <> show r)
  Left err ->
    case fromException err of
      Just (e :: OptGetFailure) ->
        withText `L.isInfixOf` (show e) @?
        ("Expected '" <> withText <> "' exception error but got: " <>
         displayException e)
      _ -> assertFailure $
           "Expected OptGetFailure exception but got: " <>
           displayException err


main :: IO ()
main = defaultMain $
       testGroup "ConfigTests"
       [ testGroup "Set and get" $ testSetAndGet
       , testGroup "Deprecated Configs" $ testDeprecated
       , testGroup "Config help" $ testHelp
       ]

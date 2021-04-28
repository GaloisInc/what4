{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

import           Control.Exception ( displayException, try, SomeException(..), fromException )
import qualified Data.List as L
import           Data.Parameterized.Context ( pattern Empty, pattern (:>) )
import           Data.Void
import           Prettyprinter

import           Test.Tasty
import           Test.Tasty.Checklist
import           Test.Tasty.HUnit

import           What4.BaseTypes
import           What4.Concrete
import           What4.Config


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
  where
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
    wantOpSetFailure withText res = case res of
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

instance TestShow (Doc Void) where testShow = show
instance TestShow [Doc Void] where testShow = testShowList


main :: IO ()
main = defaultMain $
       testGroup "ConfigTests"
       [ testGroup "Deprecated Configs" $ testDeprecated
       , testGroup "Config help" $ testHelp
       ]

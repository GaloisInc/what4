{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

import           Control.Exception ( displayException, try, SomeException(..), fromException )
import qualified Data.List as L

import           Test.Tasty
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


main :: IO ()
main = defaultMain $
       testGroup "ConfigTests"
       [ testGroup "Deprecated Configs" $ testDeprecated
       ]

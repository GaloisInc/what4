------------------------------------------------------------------------
-- |
-- Module      : What4.Config
-- Description : Declares attributes for simulator configuration settings.
-- Copyright   : (c) Galois, Inc 2015-2020
-- License     : BSD3
-- Maintainer  : Rob Dockins <rdockins@galois.com>
-- Stability   : provisional
--
-- This module provides access to persistent configuration settings, and
-- is designed for access both by Haskell client code of the What4 library,
-- and by users of the systems ultimately built using the library, for example,
-- from within a user-facing REPL.
--
-- Configurations are defined dynamically by combining a collection of
-- configuration option descriptions.  This allows disparate modules
-- to define their own configuration options, rather than having to
-- define the options for all modules in a central place.  Every
-- configuration option has a name, which consists of a nonempty
-- sequence of period-separated strings.  The intention is that option
-- names should conform to a namespace hierarchy both for
-- organizational purposes and to avoid namespace conflicts.  For
-- example, the options for an \"asdf\" module might be named as:
--
--    * asdf.widget
--    * asdf.frob
--    * asdf.max_bound
--
-- At runtime, a configuration consists of a collection of nested
-- finite maps corresponding to the namespace tree of the existing
-- options.  A configuration option may be queried or set either by
-- using a raw string representation of the name (see
-- @getOptionSettingFromText@), or by using a `ConfigOption` value
-- (using @getOptionSetting@), which provides a modicum of type-safety
-- over the basic dynamically-typed configuration maps.
--
-- Each option is associated with an \"option style\", which describes
-- the underlying type of the option (e.g., integer, boolean, string,
-- etc.) as well as the allowed settings of that value.  In addition,
-- options can take arbitrary actions when their values are changed in
-- the @opt_onset@ callback.
--
-- Every configuration comes with the built-in `verbosity`
-- configuration option pre-defined.  A `Config` value is constructed
-- using the `initialConfig` operation, which should be given the
-- initial verbosity value and a collection of configuration options
-- to install.  A configuration may be later extended with additional
-- options by using the `extendConfig` operation.
--
-- Example use (assuming you wanted to use the z3 solver):
--
-- > import What4.Solver
-- >
-- > setupSolverConfig :: (IsExprBuilder sym) -> sym -> IO ()
-- > setupSolverConfig sym = do
-- >   let cfg = getConfiguration sym
-- >   extendConfig (solver_adapter_config_options z3Adapter) cfg
-- >   z3PathSetter <- getOptionSetting z3Path
-- >   res <- setOpt z3PathSetter "/usr/bin/z3"
-- >   assert (null res) (return ())
--
-- Developer's note: we might want to add the following operations:
--
--   * a method for \"unsetting\" options to restore the default state of an option
--   * a method for removing options from a configuration altogether
--       (i.e., to undo extendConfig)
--
--
-- Note regarding concurrency: the configuration data structures in
-- this module are implemented using MVars, and may safely be used in
-- a multithreaded way; configuration changes made in one thread will
-- be visible to others in a properly synchronized way.  Of course, if
-- one desires to isolate configuration changes in different threads
-- from each other, separate configuration objects are required. The
-- @splitConfig@ operation may be useful to partially isolate
-- configuration objects.  As noted in the documentation for
-- 'opt_onset', the validation procedures for options should not look
-- up the value of other options, or deadlock may occur.
------------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module What4.Config
  ( -- * Names of properties
    ConfigOption
  , configOption
  , configOptionType
  , configOptionName
  , configOptionText
  , configOptionNameParts

    -- * Option settings
  , OptionSetting(..)
  , Opt(..)
  , setUnicodeOpt
  , setIntegerOpt
  , setBoolOpt

    -- * Defining option styles
  , OptionStyle(..)
  , set_opt_default
  , set_opt_onset

    -- ** OptionSetResult
  , OptionSetResult(..)
  , optOK
  , optWarn
  , optErr
  , checkOptSetResult
  , OptSetFailure(..)
  , OptGetFailure(..)
  , OptCreateFailure(..)

    -- ** Option style templates
  , Bound(..)
  , boolOptSty
  , integerOptSty
  , realOptSty
  , stringOptSty
  , realWithRangeOptSty
  , realWithMinOptSty
  , realWithMaxOptSty
  , integerWithRangeOptSty
  , integerWithMinOptSty
  , integerWithMaxOptSty
  , enumOptSty
  , listOptSty
  , executablePathOptSty

    -- * Describing configuration options
  , ConfigDesc
  , mkOpt
  , opt
  , optV
  , optU
  , optUV
  , copyOpt
  , deprecatedOpt

    -- * Building and manipulating configurations
  , Config
  , initialConfig
  , extendConfig
  , tryExtendConfig
  , splitConfig

  , getOptionSetting
  , getOptionSettingFromText

    -- * Extracting entire subtrees of the current configuration
  , ConfigValue(..)
  , getConfigValues

    -- * Printing help messages for configuration options
  , configHelp

    -- * Verbosity
  , verbosity
  , verbosityLogger
  ) where

import           Control.Applicative ( Const(..), (<|>) )
import           Control.Concurrent.MVar
import qualified Control.Concurrent.ReadWriteVar as RWV
import           Control.Lens ((&))
import qualified Control.Lens.Combinators as LC
import           Control.Monad (foldM, when)
import           Control.Monad.Catch
import           Control.Monad.IO.Class
import           Control.Monad.Writer.Strict (MonadWriter(..), WriterT, execWriterT)
import           Data.Foldable (toList)
import           Data.Kind
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Void
import           System.IO ( Handle, hPutStr )
import           System.IO.Error ( ioeGetErrorString )

import           Prettyprinter hiding (Unbounded)

import           What4.BaseTypes
import           What4.Concrete
import qualified What4.Utils.Environment as Env
import           What4.Utils.StringLiteral

-------------------------------------------------------------------------
-- ConfigOption

-- | A Haskell-land wrapper around the name of a configuration option.
--   Developers are encouraged to define and use `ConfigOption` values
--   to avoid two classes of errors: typos in configuration option names;
--   and dynamic type-cast failures.  Both classes of errors can be lifted
--   to statically-checkable failures (missing symbols and type-checking,
--   respectively) by consistently using `ConfigOption` values.
--
--   The following example indicates the suggested usage
--
-- @
--   asdfFrob :: ConfigOption BaseRealType
--   asdfFrob = configOption BaseRealRepr "asdf.frob"
--
--   asdfMaxBound :: ConfigOption BaseIntegerType
--   asdfMaxBound = configOption BaseIntegerRepr "asdf.max_bound"
-- @
data ConfigOption (tp :: BaseType) where
  ConfigOption :: BaseTypeRepr tp -> NonEmpty Text -> ConfigOption tp

instance Show (ConfigOption tp) where
  show = configOptionName

-- | Construct a `ConfigOption` from a string name.  Idiomatic usage is
--   to define a single top-level `ConfigOption` value in the module where the option
--   is defined to consistently fix its name and type for all subsequent uses.
configOption :: BaseTypeRepr tp -> String -> ConfigOption tp
configOption tp nm =
  case splitPath (Text.pack nm) of
    Just ps -> ConfigOption tp ps
    Nothing -> error "config options cannot have an empty name"

-- | Split a text value on \' characters.  Return @Nothing@ if
--   the whole string, or any of its segments, is the empty string.
splitPath :: Text -> Maybe (NonEmpty Text)
splitPath nm =
   let nms = Text.splitOn "." nm in
   case nms of
     (x:xs) | all (not . Text.null) (x:xs) -> Just (x:|xs)
     _ -> Nothing

-- | Get the individual dot-separated segments of an option's name.
configOptionNameParts :: ConfigOption tp -> [Text]
configOptionNameParts (ConfigOption _ (x:|xs)) = x:xs

-- | Reconstruct the original string name of this option.
configOptionName :: ConfigOption tp -> String
configOptionName = Text.unpack . configOptionText

-- | Reconstruct the original string name of this option.
configOptionText :: ConfigOption tp -> Text
configOptionText (ConfigOption _ (x:|xs)) = Text.intercalate "." $ (x:xs)

-- | Retrieve the run-time type representation of @tp@.
configOptionType :: ConfigOption tp -> BaseTypeRepr tp
configOptionType (ConfigOption tp _) = tp

------------------------------------------------------------------------------
-- OptionSetResult

-- | When setting the value of an option, a validation function is called
--   (as defined by the associated @OptionStyle@).  The result of the validation
--   function is an @OptionSetResult@.  If the option value given is invalid
--   for some reason, an error should be returned.  Additionally, warning messages
--   may be returned, which will be passed through to the eventual call site
--   attempting to alter the option setting.
data OptionSetResult =
  OptionSetResult
  { optionSetError    :: !(Maybe (Doc Void))
  , optionSetWarnings :: !(Seq (Doc Void))
  }

instance Semigroup OptionSetResult where
  x <> y = OptionSetResult
            { optionSetError    = optionSetError x <> optionSetError y
            , optionSetWarnings = optionSetWarnings x <> optionSetWarnings y
            }

instance Monoid OptionSetResult where
  mappend = (<>)
  mempty  = optOK

-- | Accept the new option value with no errors or warnings.
optOK :: OptionSetResult
optOK = OptionSetResult{ optionSetError = Nothing, optionSetWarnings = mempty }

-- | Reject the new option value with an error message.
optErr :: Doc Void -> OptionSetResult
optErr x = OptionSetResult{ optionSetError = Just x, optionSetWarnings = mempty }

-- | Accept the given option value, but report a warning message.
optWarn :: Doc Void -> OptionSetResult
optWarn x = OptionSetResult{ optionSetError = Nothing, optionSetWarnings = Seq.singleton x }


-- | An @OptionSetting@ gives the direct ability to query or set the current value
--   of an option.  The @getOption@ field is an action that, when executed, fetches
--   the current value of the option, if it is set.  The @setOption@ method attempts
--   to set the value of the option.  If the associated @opt_onset@ validation method
--   rejects the option, it will retain its previous value; otherwise it will be set
--   to the given value.  In either case, the generated @OptionSetResult@ will be
--   returned.
data OptionSetting (tp :: BaseType) =
  OptionSetting
  { optionSettingName :: ConfigOption tp
  , getOption :: IO (Maybe (ConcreteVal tp))
  , setOption :: ConcreteVal tp -> IO OptionSetResult
  }


instance Show (OptionSetting tp) where
  show = (<> " option setting") .
         LC.cons '\'' . flip LC.snoc '\'' .
         show . optionSettingName
instance ShowF OptionSetting

-- | An option defines some metadata about how a configuration option behaves.
--   It contains a base type representation, which defines the runtime type
--   that is expected for setting and querying this option at runtime.
data OptionStyle (tp :: BaseType) =
  OptionStyle
  { opt_type :: BaseTypeRepr tp
    -- ^ base type representation of this option

  , opt_onset :: Maybe (ConcreteVal tp) -> ConcreteVal tp -> IO OptionSetResult
    -- ^ An operation for validating new option values.  This action may also
    -- be used to take actions whenever an option setting is changed.  NOTE!
    -- the onset action should not attempt to look up the values of other
    -- configuration settings, or deadlock may occur.
    --
    -- The first argument is the current value of the option (if any).
    -- The second argument is the new value that is being set.
    -- If the validation fails, the operation should return a result
    -- describing why validation failed. Optionally, warnings may also be returned.

  , opt_help :: Doc Void
    -- ^ Documentation for the option to be displayed in the event a user asks for information
    --   about this option.  This message should contain information relevant to all options in this
    --   style (e.g., its type and range of expected values), not necessarily
    --   information about a specific option.

  , opt_default_value :: Maybe (ConcreteVal tp)
    -- ^ This gives a default value for the option, if set.
  }

-- | A basic option style for the given base type.
--   This option style performs no validation, has no
--   help information, and has no default value.
defaultOpt :: BaseTypeRepr tp -> OptionStyle tp
defaultOpt tp =
  OptionStyle
  { opt_type = tp
  , opt_onset = \_ _ -> return mempty
  , opt_help = mempty
  , opt_default_value = Nothing
  }

-- | Update the @opt_onset@ field.
set_opt_onset :: (Maybe (ConcreteVal tp) -> ConcreteVal tp -> IO OptionSetResult)
                 -> OptionStyle tp
                 -> OptionStyle tp
set_opt_onset f s = s { opt_onset = f }

-- | Update the @opt_help@ field.
set_opt_help :: Doc Void
             -> OptionStyle tp
             -> OptionStyle tp
set_opt_help v s = s { opt_help = v }

-- | Update the @opt_default_value@ field.
set_opt_default :: ConcreteVal tp
              -> OptionStyle tp
              -> OptionStyle tp
set_opt_default v s = s { opt_default_value = Just v }


-- | An inclusive or exclusive bound.
data Bound r = Exclusive r
             | Inclusive r
             | Unbounded

-- | Standard option style for boolean-valued configuration options
boolOptSty :: OptionStyle BaseBoolType
boolOptSty = OptionStyle BaseBoolRepr
                        (\_ _ -> return optOK)
                        "Boolean"
                        Nothing

-- | Standard option style for real-valued configuration options
realOptSty :: OptionStyle BaseRealType
realOptSty = OptionStyle BaseRealRepr
                  (\_ _ -> return optOK)
                  "ℝ"
                  Nothing

-- | Standard option style for integral-valued configuration options
integerOptSty :: OptionStyle BaseIntegerType
integerOptSty = OptionStyle BaseIntegerRepr
                  (\_ _ -> return optOK)
                  "ℤ"
                  Nothing

stringOptSty :: OptionStyle (BaseStringType Unicode)
stringOptSty = OptionStyle (BaseStringRepr UnicodeRepr)
                  (\_ _ -> return optOK)
                  "string"
                  Nothing

checkBound :: Ord a => Bound a -> Bound a -> a -> Bool
checkBound lo hi a = checkLo lo a && checkHi a hi
 where checkLo Unbounded _ = True
       checkLo (Inclusive x) y = x <= y
       checkLo (Exclusive x) y = x <  y

       checkHi _ Unbounded     = True
       checkHi x (Inclusive y) = x <= y
       checkHi x (Exclusive y) = x <  y

docInterval :: Show a => Bound a -> Bound a -> Doc ann
docInterval lo hi = docLo lo <> ", " <> docHi hi
 where docLo Unbounded      = "(-∞"
       docLo (Exclusive r)  = "(" <> viaShow r
       docLo (Inclusive r)  = "[" <> viaShow r

       docHi Unbounded      = "+∞)"
       docHi (Exclusive r)  = viaShow r <> ")"
       docHi (Inclusive r)  = viaShow r <> "]"


-- | Option style for real-valued options with upper and lower bounds
realWithRangeOptSty :: Bound Rational -> Bound Rational -> OptionStyle BaseRealType
realWithRangeOptSty lo hi = realOptSty & set_opt_onset vf
                                       & set_opt_help help
  where help = "ℝ ∈" <+> docInterval lo hi
        vf :: Maybe (ConcreteVal BaseRealType) -> ConcreteVal BaseRealType -> IO OptionSetResult
        vf _ (ConcreteReal x)
          | checkBound lo hi x = return optOK
          | otherwise          = return $ optErr $
                                 prettyRational x <+> "out of range, expected real value in"
                                                  <+> docInterval lo hi

-- | Option style for real-valued options with a lower bound
realWithMinOptSty :: Bound Rational -> OptionStyle BaseRealType
realWithMinOptSty lo = realWithRangeOptSty lo Unbounded

-- | Option style for real-valued options with an upper bound
realWithMaxOptSty :: Bound Rational -> OptionStyle BaseRealType
realWithMaxOptSty hi = realWithRangeOptSty Unbounded hi

-- | Option style for integer-valued options with upper and lower bounds
integerWithRangeOptSty :: Bound Integer -> Bound Integer -> OptionStyle BaseIntegerType
integerWithRangeOptSty lo hi = integerOptSty & set_opt_onset vf
                                              & set_opt_help help
  where help = "ℤ ∈" <+> docInterval lo hi
        vf :: Maybe (ConcreteVal BaseIntegerType) -> ConcreteVal BaseIntegerType -> IO OptionSetResult
        vf _ (ConcreteInteger x)
          | checkBound lo hi x = return optOK
          | otherwise          = return $ optErr $
                                 pretty x <+> "out of range, expected integer value in"
                                          <+> docInterval lo hi

-- | Option style for integer-valued options with a lower bound
integerWithMinOptSty :: Bound Integer -> OptionStyle BaseIntegerType
integerWithMinOptSty lo = integerWithRangeOptSty lo Unbounded

-- | Option style for integer-valued options with an upper bound
integerWithMaxOptSty :: Bound Integer -> OptionStyle BaseIntegerType
integerWithMaxOptSty hi = integerWithRangeOptSty Unbounded hi

-- | A configuration style for options that must be one of a fixed set of text values
enumOptSty :: Set Text -> OptionStyle (BaseStringType Unicode)
enumOptSty elts = stringOptSty & set_opt_onset vf
                               & set_opt_help help
  where help = group ("one of: " <+> align (sep $ map (dquotes . pretty) $ Set.toList elts))
        vf :: Maybe (ConcreteVal (BaseStringType Unicode))
           -> ConcreteVal (BaseStringType Unicode)
           -> IO OptionSetResult
        vf _ (ConcreteString (UnicodeLiteral x))
         | x `Set.member` elts = return optOK
         | otherwise = return $ optErr $
                            "invalid setting" <+> dquotes (pretty x) <>
                            ", expected one of these enums:" <+>
                            align (sep (punctuate comma (map pretty $ Set.toList elts)))

-- | A configuration syle for options that must be one of a fixed set of text values.
--   Associated with each string is a validation/callback action that will be run
--   whenever the named string option is selected.
listOptSty
  :: Map Text (IO OptionSetResult)
  -> OptionStyle (BaseStringType Unicode)
listOptSty values =  stringOptSty & set_opt_onset vf
                                  & set_opt_help help
  where help = group ("one of: " <+> align (sep $ map (dquotes . pretty . fst) $ Map.toList values))
        vf :: Maybe (ConcreteVal (BaseStringType Unicode))
           -> ConcreteVal (BaseStringType Unicode)
           -> IO OptionSetResult
        vf _ (ConcreteString (UnicodeLiteral x)) =
         fromMaybe
          (return $ optErr $
            "invalid setting" <+> dquotes (pretty x) <>
            ", expected one from this list:" <+>
            align (sep (map (pretty . fst) $ Map.toList values)))
          (Map.lookup x values)


-- | Used as a wrapper for an option that has been deprecated. If the
-- option is actually set (as opposed to just using the default value)
-- then this will emit an OptionSetResult warning that time, optionally
-- mentioning the replacement option (if specified).
--
-- There are three cases of deprecation:
-- 1. Removing an option that no longer applies
-- 2. Changing the name or heirarchical position of an option.
-- 3. #2 and also changing the type.
-- 4. Replacing an option by multiple new options (e.g. split url option
--    into hostname and port options)
--
-- In the case of #1, the option will presumably be ignored by the
-- code and the warnings are provided to allow the user to clean the
-- option from their configurations.
--
-- In the case of #2, the old option and the new option will share the
-- same value storage: changes to one can be seen via the other and
-- vice versa.  The code can be switched over to reference the new
-- option entirely, and user configurations setting the old option
-- will still work until they have been updated and the definition of
-- the old option is removed entirely.
--
--   NOTE: in order to support #2, the newer option should be declared
--   (via 'insertOption') *before* the option it deprecates.
--
-- In the case of #3, it is not possible to share storage space, so
-- during the deprecation period, the code using the option config
-- value must check both locations and decide which value to utilize.
--
-- Case #4 is an enhanced form of #3 and #2, and is generally treated
-- as #3, but adds the consideration that deprecation warnings will
-- need to advise about multiple new options.  The inverse of #4
-- (multiple options being combined to a single newer option) is just
-- treated as separate deprecations.
--
--   NOTE: in order to support #4, the newer options should all be
--   declared (via 'insertOption') *before* the options they deprecate.
--
-- Nested deprecations are valid, and replacement warnings are
-- automatically transitive to the newest options.
--
-- Any user-supplied value for the old option will result in warnings
-- emitted to the OptionSetResult for all four cases.  Code should
-- ensure that these warnings are appropriately communicated to the
-- user to allow configuration updates to occur.
--
-- Note that for #1 and #2, the overhead burden of continuing to
-- define the deprecated option is very small, so actual removal of
-- the older config can be delayed indefinitely.

deprecatedOpt :: [ConfigDesc] -> ConfigDesc -> ConfigDesc
deprecatedOpt newerOpt (ConfigDesc o sty desc oldRepl) =
  let -- note: description and setter not modified here in case this
      -- is called again to declare additional replacements (viz. case
      -- #2 above).  These will be modified in the 'insertOption' function.
      newRepl :: Maybe [ConfigDesc]
      newRepl = (newerOpt <>) <$> (oldRepl <|> Just [])
  in ConfigDesc o sty desc newRepl


-- | A configuration style for options that are expected to be paths to an executable
--   image.  Configuration options with this style generate a warning message if set to a
--   value that cannot be resolved to an absolute path to an executable file in the
--   current OS environment.
executablePathOptSty :: OptionStyle (BaseStringType Unicode)
executablePathOptSty = stringOptSty & set_opt_onset vf
                                    & set_opt_help help
  where help = "<path>"
        vf :: Maybe (ConcreteVal (BaseStringType Unicode))
           -> ConcreteVal (BaseStringType Unicode)
           -> IO OptionSetResult
        vf _ (ConcreteString (UnicodeLiteral x)) =
                 do me <- try (Env.findExecutable (Text.unpack x))
                    case me of
                       Right{} -> return $ optOK
                       Left e  -> return $ optWarn $ pretty $ ioeGetErrorString e


-- | A @ConfigDesc@ describes a configuration option before it is installed into
--   a @Config@ object.  It consists of a @ConfigOption@ name for the option,
--   an @OptionStyle@ describing the sort of option it is, and an optional
--   help message describing the semantics of this option.
data ConfigDesc where
  ConfigDesc :: ConfigOption tp  -- describes option name and type
             -> OptionStyle tp   -- option validators, help info, type and default
             -> Maybe (Doc Void) -- help text
             -> Maybe [ConfigDesc] -- Deprecation and newer replacements
             -> ConfigDesc

instance Show ConfigDesc where
  show (ConfigDesc o _ _ _) = show o

-- | The most general method for constructing a normal `ConfigDesc`.
mkOpt :: ConfigOption tp     -- ^ Fixes the name and the type of this option
      -> OptionStyle tp      -- ^ Define the style of this option
      -> Maybe (Doc Void)    -- ^ Help text
      -> Maybe (ConcreteVal tp) -- ^ A default value for this option
      -> ConfigDesc
mkOpt o sty h def = ConfigDesc o sty{ opt_default_value = def } h Nothing

-- | Construct an option using a default style with a given initial value
opt :: Pretty help
    => ConfigOption tp      -- ^ Fixes the name and the type of this option
    -> ConcreteVal tp       -- ^ Default value for the option
    -> help                 -- ^ An informational message describing this option
    -> ConfigDesc
opt o a help = mkOpt o (defaultOpt (configOptionType o))
                       (Just (pretty help))
                       (Just a)

-- | Construct an option using a default style with a given initial value.
--   Also provide a validation function to check new values as they are set.
optV :: forall tp help
      . Pretty help
     => ConfigOption tp      -- ^ Fixes the name and the type of this option
     -> ConcreteVal tp       -- ^ Default value for the option
     -> (ConcreteVal tp -> Maybe help)
         -- ^ Validation function.  Return `Just err` if the value to set
         --   is not valid.
     -> help                -- ^ An informational message describing this option
     -> ConfigDesc
optV o a vf h = mkOpt o (defaultOpt (configOptionType o)
                           & set_opt_onset onset)
                        (Just (pretty h))
                        (Just a)

   where onset :: Maybe (ConcreteVal tp) -> ConcreteVal tp -> IO OptionSetResult
         onset _ x = case vf x of
                       Nothing -> return optOK
                       Just z  -> return $ optErr $ pretty z

-- | Construct an option using a default style with no initial value.
optU :: Pretty help
     => ConfigOption tp    -- ^ Fixes the name and the type of this option
     -> help               -- ^ An informational message describing this option
     -> ConfigDesc
optU o h = mkOpt o (defaultOpt (configOptionType o)) (Just (pretty h)) Nothing

-- | Construct an option using a default style with no initial value.
--   Also provide a validation function to check new values as they are set.
optUV :: forall help tp.
   Pretty help =>
   ConfigOption tp {- ^ Fixes the name and the type of this option -} ->
   (ConcreteVal tp -> Maybe help) {- ^ Validation function.  Return `Just err` if the value to set is not valid. -} ->
   help                {- ^ An informational message describing this option -} ->
   ConfigDesc
optUV o vf h = mkOpt o (defaultOpt (configOptionType o)
                            & set_opt_onset onset)
                       (Just (pretty h))
                       Nothing
   where onset :: Maybe (ConcreteVal tp) -> ConcreteVal tp -> IO OptionSetResult
         onset _ x = case vf x of
                       Nothing -> return optOK
                       Just z  -> return $ optErr $ pretty z

-- | The copyOpt creates a duplicate ConfigDesc under a different
-- name.  This is typically used to taking a common operation and
-- modify the prefix to apply it to a more specialized role
-- (e.g. solver.strict_parsing --> solver.z3.strict_parsing).  The
-- style and help text of the input ConfigDesc are preserved, but any
-- deprecation is discarded.
copyOpt :: (Text -> Text) -> ConfigDesc -> ConfigDesc
copyOpt modName (ConfigDesc o@(ConfigOption ty _) sty h _) =
  let newName = case splitPath (modName (configOptionText o)) of
        Just ps -> ps
        Nothing -> error "new config option must not be empty"
  in ConfigDesc (ConfigOption ty newName) sty h Nothing



------------------------------------------------------------------------
-- ConfigState

data ConfigLeaf where
  ConfigLeaf ::
    !(OptionStyle tp)              {- Style for this option -} ->
    MVar (Maybe (ConcreteVal tp))  {- State of the option -} ->
    Maybe (Doc Void)               {- Help text for the option -} ->
    ConfigLeaf

-- | Main configuration data type.  It is organized as a trie based on the
--   name segments of the configuration option name.
data ConfigTrie where
  ConfigTrie ::
    !(Maybe ConfigLeaf) ->
    !ConfigMap ->
    ConfigTrie

type ConfigMap = Map Text ConfigTrie

freshLeaf :: [Text] -> ConfigLeaf -> ConfigTrie
freshLeaf [] l     = ConfigTrie (Just l) mempty
freshLeaf (a:as) l = ConfigTrie Nothing (Map.singleton a (freshLeaf as l))

-- | The given list of name segments defines a lens into a config trie.
adjustConfigTrie :: Functor t => [Text] -> (Maybe ConfigLeaf -> t (Maybe ConfigLeaf)) -> Maybe (ConfigTrie) -> t (Maybe ConfigTrie)
adjustConfigTrie     as f Nothing                 = fmap (freshLeaf as) <$> f Nothing
adjustConfigTrie (a:as) f (Just (ConfigTrie x m)) = Just . ConfigTrie x <$> adjustConfigMap a as f m
adjustConfigTrie     [] f (Just (ConfigTrie x m)) = g <$> f x
  where g Nothing | Map.null m = Nothing
        g x' = Just (ConfigTrie x' m)

-- | The given nonempty list of name segments (with the initial segment given as the first argument)
--   defines a lens into a @ConfigMap@.
adjustConfigMap :: Functor t => Text -> [Text] -> (Maybe ConfigLeaf -> t (Maybe ConfigLeaf)) -> ConfigMap -> t ConfigMap
adjustConfigMap a as f = Map.alterF (adjustConfigTrie as f) a

-- | Traverse an entire @ConfigMap@.  The first argument is the
-- reversed heirarchical location of the starting map entry location.
traverseConfigMap ::
  Applicative t =>
  [Text] {- ^ A REVERSED LIST of the name segments that represent the context from the root to the current @ConfigMap@. -} ->
  ([Text] -> ConfigLeaf -> t ConfigLeaf) {- ^ An action to apply to each leaf. The path to the leaf is provided. -} ->
  ConfigMap {- ^ ConfigMap to traverse -} ->
  t ConfigMap
traverseConfigMap revPath f = Map.traverseWithKey (\k -> traverseConfigTrie (k:revPath) f)

-- | Traverse an entire @ConfigTrie@.
traverseConfigTrie ::
  Applicative t =>
  [Text] {- ^ A REVERSED LIST of the name segments that represent the context from the root to the current @ConfigTrie@. -} ->
  ([Text] -> ConfigLeaf -> t ConfigLeaf) {- ^ An action to apply to each leaf. The path to the leaf is provided. -} ->
  ConfigTrie {- ^ @ConfigTrie@ to traverse -} ->
  t ConfigTrie
traverseConfigTrie revPath f (ConfigTrie x m) =
  ConfigTrie <$> traverse (f (reverse revPath)) x <*> traverseConfigMap revPath f m

-- | Traverse a subtree of a @ConfigMap@.  If an empty path is provided, the entire @ConfigMap@ will
--   be traversed.
traverseSubtree ::
  Applicative t =>
  [Text] {- ^ Path indicating the subtree to traverse -} ->
  ([Text] -> ConfigLeaf -> t ConfigLeaf) {- ^ Action to apply to each leaf in the indicated subtree.  The path to the leaf is provided. -} ->
  ConfigMap {- ^ @ConfigMap@ to traverse -} ->
  t ConfigMap
traverseSubtree ps0 f = go ps0 []
  where
  go     [] revPath = traverseConfigMap revPath f
  go (p:ps) revPath = Map.alterF (traverse g) p
     where g (ConfigTrie x m) = ConfigTrie <$> here x <*> go ps (p:revPath) m
           here = traverse (f (reverse (p:revPath)))


-- | Add an option to the given @ConfigMap@.  If the
--   option cannot be added (because it already exists
--   in the map) the map is instead returned unchanged.
tryInsertOption ::
  (MonadIO m, MonadCatch m) =>
  ConfigMap -> ConfigDesc -> m ConfigMap
tryInsertOption m d =
  catch (insertOption m d)
    (\OptCreateFailure{} -> return m)

-- | Add an option to the given @ConfigMap@ or throws an
-- 'OptCreateFailure' exception on error.
--
-- Inserting an option multiple times is idempotent under equivalency
-- modulo the opt_onset in the option's style, otherwise it is an
-- error.
insertOption ::
  (MonadIO m, MonadThrow m) =>
  ConfigMap -> ConfigDesc -> m ConfigMap
insertOption m d@(ConfigDesc o@(ConfigOption _tp (p:|ps)) sty h newRepls) =
  adjustConfigMap p ps f m
  where
  f Nothing =
    let addOnSetWarning warning oldSty =
          let newSty = set_opt_onset depF oldSty
              oldVF = opt_onset oldSty
              depF oldV newV =
                do v <- oldVF oldV newV
                   return (v <> optWarn warning)
          in newSty
        deprHelp depMsg ontoHelp =
          let hMod oldHelp = vsep [ oldHelp, "*** DEPRECATED! ***", depMsg ]
          in hMod <$> ontoHelp
        newRefs tySep = hsep . punctuate comma .
                        map (\(n, ConfigLeaf s _ _) -> optRef tySep n s)
        optRef tySep nm s = hcat [ pretty (show nm), tySep
                                 , pretty (show (opt_type s))
                                 ]
    in case newRepls of
         -- not deprecated
         Nothing ->
           do ref <- liftIO (newMVar (opt_default_value sty))
              return (Just (ConfigLeaf sty ref h))

         -- deprecation case #1 (removal)
         Just [] ->
           do ref <- liftIO (newMVar (opt_default_value sty))
              let sty' = addOnSetWarning
                         ("DEPRECATED CONFIG OPTION WILL BE IGNORED: " <>
                           pretty (show o) <>
                           " (no longer valid)")
                         sty
                  hmsg = "Option '" <> pretty (show o) <> "' is no longer valid."
              return (Just (ConfigLeaf sty' ref (deprHelp hmsg h)))

         Just n -> do
           let newer =
                 let returnFnd fnd loc lf =
                       if name loc == fnd
                       then Const [Just (fnd, lf)]
                       else Const [Nothing]
                     name parts = Text.intercalate "." parts
                     lookupNewer (ConfigDesc (ConfigOption _ (t:|ts)) _sty _h new2) =
                       case new2 of
                         Nothing -> getConst $ traverseConfigMap [] (returnFnd (name (t:ts))) m
                         Just n2 -> concat (lookupNewer <$> n2)
                 in lookupNewer <$> n
               chkMissing opts =
                 if not (null opts) && null (catMaybes opts)
                 then throwM $ OptCreateFailure d $
                      "replacement options must be inserted into" <>
                      " Config before this deprecated option"
                 else return opts
           newOpts <- catMaybes . concat <$> mapM chkMissing newer

           case newOpts of

             -- deprecation case #1 (removal)
             [] ->
               do ref <- liftIO (newMVar (opt_default_value sty))
                  let sty' = addOnSetWarning
                             ("DEPRECATED CONFIG OPTION WILL BE IGNORED: " <>
                              pretty (show o) <>
                              " (no longer valid)")
                             sty
                      hmsg = "Option '" <> pretty (show o) <> "' is no longer valid."
                  return (Just (ConfigLeaf sty' ref (deprHelp hmsg h)))

             -- deprecation case #2 (renamed)
             ((nm, ConfigLeaf sty' v _):[])
               | Just Refl <- testEquality (opt_type sty) (opt_type sty') ->
                 do let updSty = addOnSetWarning
                                 ("DEPRECATED CONFIG OPTION USED: " <>
                                  pretty (show o) <>
                                  " (renamed to: " <> pretty nm <> ")")
                        hmsg = "Suggest replacing '" <> pretty (show o) <>
                               "' with '" <> pretty nm <> "'."
                    return (Just (ConfigLeaf (updSty sty) v (deprHelp hmsg h)))

             -- deprecation case #3 (renamed and re-typed)
             (new1:[]) ->
               do ref <- liftIO (newMVar (opt_default_value sty))
                  let updSty = addOnSetWarning
                               ("DEPRECATED CONFIG OPTION USED: " <>
                                optRef "::" o sty <>
                                " (changed to: " <>
                                newRefs "::" [new1] <>
                                "); this value may be ignored")
                      hmsg = "Suggest converting '" <>
                             optRef " of type " o sty <>
                             " to " <>
                             newRefs " of type " [new1]
                  return (Just (ConfigLeaf (updSty sty) ref (deprHelp hmsg h)))

             -- deprecation case #4 (split to multiple options)
             newMulti ->
               do ref <- liftIO (newMVar (opt_default_value sty))
                  let updSty = addOnSetWarning
                               ("DEPRECATED CONFIG OPTION USED: " <>
                                optRef "::" o sty <>
                                " (replaced by: " <>
                                newRefs "::" newMulti <>
                                "); this value may be ignored")
                      hmsg = "Suggest converting " <>
                             optRef " of type " o sty <>
                             " to: " <> (newRefs " of type " newMulti)
                  return (Just (ConfigLeaf (updSty sty) ref (deprHelp hmsg h)))

  f (Just existing@(ConfigLeaf sty' _ h')) =
    case testEquality (opt_type sty) (opt_type sty') of
      Just Refl ->
        if and [ show (opt_help sty) == show (opt_help sty')
               , opt_default_value sty == opt_default_value sty'
               -- Note opt_onset in sty is ignored/dropped
               , show h == show h'
               ]
        then return $ Just existing
        else throwM $ OptCreateFailure d "already exists"
      Nothing -> throwM $ OptCreateFailure d
                 (pretty $ "already exists with type " <> show (opt_type sty'))

data OptCreateFailure = OptCreateFailure ConfigDesc (Doc Void)

instance Exception OptCreateFailure
instance Show OptCreateFailure where
  show (OptCreateFailure cfgdesc msg) =
    "Failed to create option " <> show cfgdesc <> ": " <> show msg


------------------------------------------------------------------------
-- Config

-- | The main configuration datatype.  It consists of a Read/Write var
--   containing the actual configuration data.
newtype Config = Config (RWV.RWVar ConfigMap)

-- | Construct a new configuration from the given configuration
--   descriptions.
initialConfig ::
  Integer      {- ^ Initial value for the `verbosity` option -} ->
  [ConfigDesc] {- ^ Option descriptions to install -} ->
  IO (Config)
initialConfig initVerbosity ts = do
   cfg <- Config <$> RWV.new Map.empty
   extendConfig (builtInOpts initVerbosity ++ ts) cfg
   return cfg

-- | Extend an existing configuration with new options.  An
--   'OptCreateFailure' exception will be raised if any of the given
--   options clash with options that already exists.
extendConfig :: [ConfigDesc] -> Config -> IO ()
extendConfig ts (Config cfg) =
  RWV.modify_ cfg (\m -> foldM insertOption m ts)


-- | Extend an existing configuration with new options. If any
--   of the given options are already present in the configuration,
--   nothing is done for that option and it is silently skipped.
tryExtendConfig :: [ConfigDesc] -> Config -> IO ()
tryExtendConfig ts (Config cfg) =
  RWV.modify_ cfg (\m -> foldM tryInsertOption m ts)

-- | Create a new configuration object that shares the option
--   settings currently in the given input config. However,
--   any options added to either configuration using @extendConfig@
--   will not be propagated to the other.
--
--   Option settings that already exist in the input configuration
--   will be shared between both; changes to those options will be
--   visible in both configurations.
splitConfig :: Config -> IO Config
splitConfig (Config cfg) = Config <$> (RWV.with cfg RWV.new)

-- | Verbosity of the simulator.  This option controls how much
--   informational and debugging output is generated.
--   0 yields low information output; 5 is extremely chatty.
verbosity :: ConfigOption BaseIntegerType
verbosity = configOption BaseIntegerRepr "verbosity"

-- | Built-in options that are installed in every @Config@ object.
builtInOpts :: Integer -> [ConfigDesc]
builtInOpts initialVerbosity =
  [ opt verbosity
        (ConcreteInteger initialVerbosity)
        ("Verbosity of the simulator: higher values produce more detailed informational and debugging output." :: Text)
  ]

-- | Return an operation that will consult the current value of the
--   verbosity option, and will print a string to the given @Handle@
--   if the provided int is smaller than the current verbosity setting.
verbosityLogger :: Config -> Handle -> IO (Int -> String -> IO ())
verbosityLogger cfg h =
  do verb <- getOptionSetting verbosity cfg
     return $ \n msg ->
       do v <- getOpt verb
          when (toInteger n < v) (hPutStr h msg)

-- | A utility class for making working with option settings
--   easier.  The @tp@ argument is a @BaseType@, and the @a@
--   argument is an associcated Haskell type.
class Opt (tp :: BaseType) (a :: Type) | tp -> a where
  -- | Return the current value of the option, as a @Maybe@ value.
  getMaybeOpt :: OptionSetting tp -> IO (Maybe a)

  -- | Attempt to set the value of an option.  Return any errors
  --   or warnings.
  trySetOpt :: OptionSetting tp -> a -> IO OptionSetResult

  -- | Set the value of an option.  Return any generated warnings.
  --   Throws an OptSetFailure exception if a validation error occurs.
  setOpt :: OptionSetting tp -> a -> IO [Doc Void]
  setOpt x v = trySetOpt x v >>= checkOptSetResult x

  -- | Get the current value of an option.  Throw an exception
  --   if the option is not currently set.
  getOpt :: OptionSetting tp -> IO a
  getOpt x = maybe (throwM $ OptGetFailure (OSet $ Some x) "not set") return
             =<< getMaybeOpt x

-- | Throw an exception if the given @OptionSetResult@ indicates
--   an error.  Otherwise, return any generated warnings.
checkOptSetResult :: OptionSetting tp -> OptionSetResult -> IO [Doc Void]
checkOptSetResult optset res =
  case optionSetError res of
    Just msg -> throwM $ OptSetFailure (Some optset) msg
    Nothing -> return (toList (optionSetWarnings res))

data OptSetFailure = OptSetFailure (Some OptionSetting) (Doc Void)
instance Exception OptSetFailure
instance Show OptSetFailure where
  show (OptSetFailure optset msg) =
    "Failed to set " <> show optset <> ": " <> show msg

data OptRef = OName Text | OSet (Some OptionSetting) | OCfg (Some ConfigOption)
instance Show OptRef where
  show = \case
    OName t -> show t
    OSet (Some s) -> show s
    OCfg (Some c) -> show c

data OptGetFailure = OptGetFailure OptRef (Doc Void)
instance Exception OptGetFailure
instance Show OptGetFailure where
  show (OptGetFailure optref msg) =
    "Failed to get " <> (show optref) <> ": " <> show msg


instance Opt (BaseStringType Unicode) Text where
  getMaybeOpt x = fmap (fromUnicodeLit . fromConcreteString) <$> getOption x
  trySetOpt x v = setOption x (ConcreteString (UnicodeLiteral v))

instance Opt BaseIntegerType Integer where
  getMaybeOpt x = fmap fromConcreteInteger <$> getOption x
  trySetOpt x v = setOption x (ConcreteInteger v)

instance Opt BaseBoolType Bool where
  getMaybeOpt x = fmap fromConcreteBool <$> getOption x
  trySetOpt x v = setOption x (ConcreteBool v)

instance Opt BaseRealType Rational where
  getMaybeOpt x = fmap fromConcreteReal <$> getOption x
  trySetOpt x v = setOption x (ConcreteReal v)

-- | Given a unicode text value, set the named option to that value or
-- generate an OptSetFailure exception if the option is not a unicode
-- text valued option.
setUnicodeOpt :: Some OptionSetting -> Text -> IO [Doc Void]
setUnicodeOpt (Some optset) val =
  let tyOpt = configOptionType (optionSettingName optset)
  in case testEquality tyOpt (BaseStringRepr UnicodeRepr) of
       Just Refl -> setOpt optset val
       Nothing ->
         checkOptSetResult optset $ optErr $
         "option type is a" <+> pretty tyOpt <+> "but given a text string"

-- | Given an integer value, set the named option to that value or
-- generate an OptSetFailure exception if the option is not an integer
-- valued option.
setIntegerOpt :: Some OptionSetting -> Integer -> IO [Doc Void]
setIntegerOpt (Some optset) val =
  let tyOpt = configOptionType (optionSettingName optset)
  in case testEquality tyOpt BaseIntegerRepr of
       Just Refl -> setOpt optset val
       Nothing ->
         checkOptSetResult optset $ optErr $
         "option type is a" <+> pretty tyOpt <+> "but given an integer"

-- | Given a boolean value, set the named option to that value or
-- generate an OptSetFailure exception if the option is not a boolean
-- valued option.
setBoolOpt :: Some OptionSetting -> Bool -> IO [Doc Void]
setBoolOpt (Some optset) val =
  let tyOpt = configOptionType (optionSettingName optset)
  in case testEquality tyOpt BaseBoolRepr of
       Just Refl -> setOpt optset val
       Nothing ->
         checkOptSetResult optset $ optErr $
         "option type is a" <+> pretty tyOpt <+> "but given a boolean"


-- | Given a @ConfigOption@ name, produce an @OptionSetting@
--   object for accessing and setting the value of that option.
--
--   An exception is thrown if the named option cannot be found
--   the @Config@ object, or if a type mismatch occurs.
getOptionSetting ::
  ConfigOption tp ->
  Config ->
  IO (OptionSetting tp)
getOptionSetting o@(ConfigOption tp (p:|ps)) (Config cfg) =
   RWV.with cfg (getConst . adjustConfigMap p ps f)

 where
  f Nothing  = Const (throwM $ OptGetFailure (OCfg $ Some o) "not found")
  f (Just x) = Const (leafToSetting x)

  leafToSetting (ConfigLeaf sty ref _h)
    | Just Refl <- testEquality (opt_type sty) tp = return $
      OptionSetting
      { optionSettingName = o
      , getOption  = readMVar ref
      , setOption = \v -> modifyMVar ref $ \old ->
          do res <- opt_onset sty old v
             let new = if (isJust (optionSetError res)) then old else (Just v)
             new `seq` return (new, res)
      }
    | otherwise = throwM $ OptGetFailure (OCfg $ Some o)
                  (pretty $ "Type mismatch: " <>
                    "expected '" <> show tp <>
                    "' but found '" <> show (opt_type sty) <> "'"
                  )

-- | Given a text name, produce an @OptionSetting@
--   object for accessing and setting the value of that option.
--
--   An exception is thrown if the named option cannot be found.
getOptionSettingFromText ::
  Text ->
  Config ->
  IO (Some OptionSetting)
getOptionSettingFromText nm (Config cfg) =
   case splitPath nm of
     Nothing -> throwM $ OptGetFailure (OName "") "Illegal empty name for option"
     Just (p:|ps) -> RWV.with cfg (getConst . adjustConfigMap p ps (f (p:|ps)))
  where
  f (p:|ps) Nothing  = Const (throwM $ OptGetFailure
                              (OName (Text.intercalate "." (p:ps)))
                              "not found")
  f path (Just x) = Const (leafToSetting path x)

  leafToSetting path (ConfigLeaf sty ref _h) = return $
    Some OptionSetting
         { optionSettingName = ConfigOption (opt_type sty) path
         , getOption = readMVar ref
         , setOption = \v -> modifyMVar ref $ \old ->
             do res <- opt_onset sty old v
                let new = if (isJust (optionSetError res)) then old else (Just v)
                new `seq` return (new, res)
         }


-- | A @ConfigValue@ bundles together the name of an option with its current value.
data ConfigValue where
  ConfigValue :: ConfigOption tp -> ConcreteVal tp -> ConfigValue

instance Pretty ConfigValue where
  pretty (ConfigValue option val) =
    ppSetting (configOptionNameParts option) (Just val)
    <+> "::" <+> pretty (configOptionType option)


-- | Given the name of a subtree, return all
--   the currently-set configuration values in that subtree.
--
--   If the subtree name is empty, the entire tree will be traversed.
getConfigValues ::
  Text ->
  Config ->
  IO [ConfigValue]
getConfigValues prefix (Config cfg) =
  RWV.with cfg $ \m ->
  do let ps = dropWhile Text.null $ Text.splitOn "." prefix
         f :: [Text] -> ConfigLeaf -> WriterT (Seq ConfigValue) IO ConfigLeaf
         f [] _ = throwM $ OptGetFailure (OName prefix)
                  "illegal empty option prefix name"
         f (p:path) l@(ConfigLeaf sty ref _h) =
            do liftIO (readMVar ref) >>= \case
                 Just x  -> tell (Seq.singleton (ConfigValue (ConfigOption (opt_type sty) (p:|path)) x))
                 Nothing -> return ()
               return l
     toList <$> execWriterT (traverseSubtree ps f m)


ppSetting :: [Text] -> Maybe (ConcreteVal tp) -> Doc ann
ppSetting nm v = fill 30 (pretty (Text.intercalate "." nm)
                           <> maybe mempty (\x -> " = " <> ppConcrete x) v
                         )

ppOption :: [Text] -> OptionStyle tp -> Maybe (ConcreteVal tp) -> Maybe (Doc Void) -> Doc Void
ppOption nm sty x help =
  vcat
  [ group $ fillCat [ppSetting nm x, indent 2 (opt_help sty)]
  , maybe mempty (indent 4) help
  ]

ppConfigLeaf :: [Text] -> ConfigLeaf -> IO (Doc Void)
ppConfigLeaf nm (ConfigLeaf sty ref help) =
  do x <- readMVar ref
     return $ ppOption nm sty x help

-- | Given the name of a subtree, compute help text for
--   all the options available in that subtree.
--
--   If the subtree name is empty, the entire tree will be traversed.
configHelp ::
  Text ->
  Config ->
  IO [Doc Void]
configHelp prefix (Config cfg) =
  RWV.with cfg $ \m ->
  do let ps = dropWhile Text.null $ Text.splitOn "." prefix
         f :: [Text] -> ConfigLeaf -> WriterT (Seq (Doc Void)) IO ConfigLeaf
         f nm leaf = do d <- liftIO (ppConfigLeaf nm leaf)
                        tell (Seq.singleton d)
                        return leaf
     toList <$> (execWriterT (traverseSubtree ps f m))

prettyRational :: Rational -> Doc ann
prettyRational = viaShow

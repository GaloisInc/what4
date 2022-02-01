{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}

{- |
Module      : Test.Verification
Description : Testing abstraction layer
Copyright   : (c) Galois Inc, 2020
License     : BSD3
Maintainer  : kquick@galois.com

This is a testing abstraction layer that allows the integration of
test properties and functions into the What4 library without requiring
a binding to a specific testing library or version thereof
(e.g. QuickCheck, Hedgehog, etc.).  All test properties and functions
should be specified using the primary set of functions in this module,
and then the actual test code will specify a binding of these
abstractions to a specific test library.

In this way, the What4 can implement not only local tests but the test
functionality can be exported to enable downstream modules to perform
extended testing.

The actual tests should be written using only the functions exported
in the testing exports section of this module.  Note that only the set
of functions needed for What4 is defined by this testing abstraction;
if additional testing functions are needed, the GenEnv context should be
extended to add an adaptation entry and the function should be defined
here for use by the tests.

The overlap (common subset) between testing libraries such as
QuickCheck and Hedgehog is only of moderate size: both libraries (and
especially Hedgehog) provide functionality that is not present in the
other library.  This module does not attempt to provide full coverage
for the functionality in both libraries; the intent is that test
functions can be written using the proxy functions defined here and
that downstream code using either of QuickCheck or Hedgehog can
utilize these support functions in their own tests.  As such, it is
recommended that the What4 integrated tests are limited in expression
to the common subset that can be described here.

A specific test configuration will need to use the functions and
definitions in the concretization exports to bind these abstracted
test functions to the specific library being used by that test suite.

For example, to bind to QuickCheck, specify:

> import QuickCheck
> import qualified Test.Verification as V
>
> quickCheckGenerators = V.GenEnv { V.genChooseBool = elements [ True, False ]
>                                 , V.genChooseInteger = \r -> choose r
>                                 , V.genChooseInt = \r -> choose r
>                                 , V.genGetSize = getSize
>                                 }
>
> genTest :: String -> V.Gen V.Property -> TestTree
> genTest nm p = testProperty nm
>                (property $ V.toNativeProperty quickCheckGenerators p)

-}

module Test.Verification
  (
    -- * Testing definitions

    -- | These definitions should be used by the tests themselves.  Most
    -- of these parallel a corresponding function in QuickCheck or
    -- Hedgehog, so the adaptation is minimal.
    assuming
  , (==>)
  , property
  , chooseBool
  , chooseInt
  , chooseInteger
  , Gen
  , getSize
  , Verifiable(..)

    -- * Test concretization

    -- | Used by test implementation functions to map from this
    -- Verification abstraction to the actual test mechanism
    -- (e.g. QuickCheck, HedgeHog, etc.)
  , Property(..)
  , Assumption(..)
  , GenEnv(..)
  , toNativeProperty
  )
where

import Control.Monad.Trans (lift)
import Control.Monad.Trans.Reader

-- | Local definition of a Property: intended to be a proxy for a
-- QuickCheck Property or a Hedgehog Property.  The 'toNativeProperty'
-- implementation function converts from these proxy Properties to the
-- native Property implementation.
--
-- Tests should only use the 'Property' type as an output; the
-- constructors and internals should be used only by the test
-- concretization.
data Property = BoolProperty Bool
              | AssumptionProp Assumption
  deriving Show

-- | A class specifying things that can be verified by constructing a
-- local Property.
class Verifiable prop where
  verifying :: prop -> Property

instance Verifiable Bool where verifying = BoolProperty

-- | Used by testing code to assert a boolean property.
property :: Bool -> Property
property = verifying

-- | Internal data structure to store the two elements to the '==>'
-- assumption operator.
data Assumption  = Assuming { preCondition :: Bool,
                              assumedProp :: Property }
  deriving Show


-- | The named form of the '==>' assumption operator
assuming :: Verifiable t => Bool -> t -> Property
assuming precond test = AssumptionProp $ Assuming precond $ verifying test

-- | The assumption operator that performs the property test (second
-- element) only when the first argument is true (the assumption guard
-- for the test).  This is the analog to the corresponding QuickCheck
-- ==> operator.
(==>) :: Verifiable t => Bool -> t -> Property
(==>) = assuming
infixr 0 ==>


instance Verifiable Property where
  verifying = id

-- ----------------------------------------------------------------------

-- | This is the reader environment for the surface level proxy
-- testing monad.  This environment will be provided by the actual
-- test code to map these proxy operations to the specific testing
-- implementation.
data GenEnv m = GenEnv { genChooseBool :: m Bool
                       , genChooseInt :: (Int, Int) -> m Int
                       , genChooseInteger :: (Integer, Integer) -> m Integer
                       , genGetSize :: m Int
                       }

-- | This is the generator monad for the Verification proxy tests.
-- The inner monad will be the actual test implementation's monadic
-- generator, and the 'a' return type is the type returned by running
-- this monad.
--
-- Tests should only use the 'Gen TYPE' as an output; the
-- constructors and internals should be used only by the test
-- concretization.
newtype Gen a =
  Gen { unGen :: forall m. Monad m => ReaderT (GenEnv m) m a }

instance Functor Gen where
  fmap f (Gen m) = Gen (fmap f m)

instance Applicative Gen where
  pure x = Gen (pure x)
  (Gen f) <*> (Gen x) = Gen (f <*> x)

instance Monad Gen where
  Gen x >>= f = Gen (x >>= \x' -> unGen (f x'))

-- | A test generator that returns True or False
chooseBool :: Gen Bool
chooseBool = Gen (asks genChooseBool >>= lift)

-- | A test generator that returns an 'Int' value between the
-- specified (inclusive) bounds.
chooseInt :: (Int, Int) -> Gen Int
chooseInt r = Gen (asks genChooseInt >>= lift . ($ r))

-- | A test generator that returns an 'Integer' value between the
-- specified (inclusive) bounds.
chooseInteger :: (Integer, Integer) -> Gen Integer
chooseInteger r = Gen (asks genChooseInteger >>= lift . ($ r))

-- | A test generator that returns the current shrink size of the
-- generator functionality.
getSize :: Gen Int
getSize = Gen (asks genGetSize >>= lift)

-- | This function should be called by the testing code to convert the
-- proxy tests in this module into the native tests (e.g. QuickCheck
-- or Hedgehog).  This function is provided with the mapping
-- environment between the proxy tests here and the native
-- equivalents, and a local Generator monad expression, returning a
-- native Generator equivalent.
toNativeProperty :: Monad m => GenEnv m -> Gen b -> m b
toNativeProperty gens (Gen gprops) = runReaderT gprops gens

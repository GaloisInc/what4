-- | Like "Test.Tasty.Hedgehog", but instead exposing an alternative
-- implementation of 'testProperty' that does not induce deprecation warnings.
module Test.Tasty.Hedgehog.Alt
  ( module TTH
  , testProperty
  ) where

import Data.String (IsString(fromString))
import Hedgehog (Property)
import Test.Tasty (TestName, TestTree)
import Test.Tasty.Hedgehog as TTH hiding (testProperty)

-- | Create a 'T.TestTree' from a Hedgehog 'Property'.
--
-- Note that @tasty-hedgehog@'s version of 'testProperty' has been deprecated
-- in favor of 'testPropertyNamed', whose second argument is intended to
-- represent the name of a top-level 'Property' value to run in the event that
-- the test fails. See https://github.com/qfpl/tasty-hedgehog/pull/42.
--
-- That being said, @what4@ currently does not define any of the properties
-- that it tests as top-level values, and it would be a pretty significant
-- undertaking to migrate all of the properties to top-level values. In the
-- meantime, we avoid incurring deprecation warnings by defining our own
-- version of 'testProperty'. The downside to this workaround is that if a
-- property fails, the error message it will produce will likely suggest
-- running ill-formed Haskell code, so users will have to use context clues to
-- determine how to /actually/ reproduce the error.
testProperty :: TestName -> Property -> TestTree
testProperty name = testPropertyNamed name (fromString name)

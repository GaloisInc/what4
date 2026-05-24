{-
Module      : TestCoverage
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Test-coverage tests: tests that require certain other tests to exist.

These guard against drift between the Cryptol specification (in @doc\/*.cry@),
the Haskell @correct_*@ predicates that transliterate it (in "What4.Domains.BV"
and submodules), and the property-based tests that exercise those predicates (in
@test\/BVDomTests.hs@).

Two correspondences are checked:

  * Cryptol \<-\> Haskell: bidirectional. Every property defined in the Cryptol
    specs has a same-named Haskell property, or is on an explicit allowlist
    of predicates that are intentionally not translated; and conversely
    every Haskell property has a same-named Cryptol counterpart, or is on a
    Haskell-only allowlist.

  * Haskell \<-\> PBT: every Haskell property defined in the abstract-domain
    modules is invoked at least once in @BVDomTests.hs@. Note: the reverse
    direction (test invokes a non-existent Haskell predicate) is trivially
    enforced by GHC.

The allowlists are small and documented inline; growing them should be a
deliberate choice. Files are read at test-runtime relative to the package root
(which is the working directory used by @cabal test@).
-}

{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import           Control.Monad (forM)
import           Data.Char (isAlphaNum)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Test.Tasty as TT
import           Test.Tasty.HUnit

-- | A Haskell source file holding properties, together with the qualifier under
-- which the test driver imports it, and the test file that should invoke its
-- properties.
data HsModule = HsModule
  { hsModFile :: FilePath
  , hsModQual :: Text
  , hsModTestFile :: FilePath
  }

arithMod, bitwiseMod, xorMod, overallMod, clpMod, stridedMod :: HsModule
arithMod   = HsModule "src/What4/Domains/BV/Arith.hs"           "A" "test/BVDomTests.hs"
bitwiseMod = HsModule "src/What4/Domains/BV/Bitwise.hs"         "B" "test/BVDomTests.hs"
xorMod     = HsModule "src/What4/Domains/BV/XOR.hs"             "X" "test/BVDomTests.hs"
overallMod = HsModule "src/What4/Domains/BV.hs"                 "O" "test/BVDomTests.hs"
clpMod     = HsModule "src/What4/Domains/BV/CLP.hs"             "C" "test/CLP.hs"
stridedMod = HsModule "src/What4/Domains/BV/StridedInterval.hs" "S" "test/StridedInterval.hs"

allHsModules :: [HsModule]
allHsModules =
  [arithMod, bitwiseMod, xorMod, overallMod, clpMod, stridedMod]

cryptolFiles :: [FilePath]
cryptolFiles =
  [ "doc/arithdomain.cry"
  , "doc/bitsdomain.cry"
  , "doc/xordomain.cry"
  , "doc/bvdomain.cry"
  , "doc/clp.cry"
  , "doc/strideddomain.cry"
  ]

main :: IO ()
main = TT.defaultMain $ TT.testGroup "Test coverage"
  [ haskellInvocationTests
  , cryptolCorrespondenceTests
  ]

------------------------------------------------------------------------
-- Haskell <-> PBT correspondence: every Haskell property is invoked from
-- BVDomTests

haskellInvocationTests :: TT.TestTree
haskellInvocationTests = TT.testGroup "Haskell predicates are invoked"
  [ testCase (hsModFile m) (checkModuleInvoked m) | m <- allHsModules ]

checkModuleInvoked :: HsModule -> Assertion
checkModuleInvoked m = do
  src     <- TIO.readFile (hsModFile m)
  testSrc <- TIO.readFile (hsModTestFile m)
  let names = extractHsPredicates src
  assertNonEmpty (hsModFile m) "Property" names
  let missing = [ n | n <- names, not (isInvokedAs (hsModQual m) n testSrc) ]
  case missing of
    [] -> pure ()
    _  -> assertFailure $ T.unpack $ T.unlines $
            ("Predicates defined in " <> T.pack (hsModFile m)
             <> " but never invoked as " <> hsModQual m <> ".<name> in "
             <> T.pack (hsModTestFile m) <> ":")
            : map ("  " <>) (Set.toAscList (Set.fromList missing))

-- | Sanity check: the source extractor should always find at least one property
-- in each scanned file. An empty result usually means the extractor is broken
-- (e.g., signature syntax changed).
assertNonEmpty :: FilePath -> Text -> [a] -> Assertion
assertNonEmpty f tyName xs =
  case xs of
    [] -> assertFailure $ T.unpack $
            "TestCoverage extractor found no " <> tyName
            <> " predicates in " <> T.pack f
            <> " - the extractor may be broken or the file is empty."
    _  -> pure ()

-- | True if @qual.name@ appears in @src@ as a token (not as a prefix of a
-- longer identifier).
isInvokedAs :: Text -> Text -> Text -> Bool
isInvokedAs qual name src = go src
  where
    needle = qual <> "." <> name
    go t =
      case T.breakOn needle t of
        (_, rest)
          | T.null rest -> False
          | otherwise ->
              let suffix = T.drop (T.length needle) rest in
              case T.uncons suffix of
                Just (c, _) | isIdentChar c -> go suffix
                _ -> True

------------------------------------------------------------------------
-- Cryptol <-> Haskell correspondence: every Cryptol property has a Haskell
-- counterpart and vice versa

-- | Cryptol predicates that are intentionally not translated into a Haskell
-- property.
--
-- @ule@\/@sle@: Haskell's three-valued @ult@\/@slt :: Maybe Bool@ already
-- covers the strict-less-than direction; supporting Cryptol's @ule@\/@sle@
-- would require new public functions.
--
-- @shrinkRange@: There is no separate @shrinkRange@ helper on the Haskell side.
cryptolOnly :: Set.Set Text
cryptolOnly = Set.fromList
  [ "correct_ule"
  , "correct_sle"
  , "correct_shrinkRange"
  ]

-- | Haskell predicates that intentionally have no Cryptol counterpart.
--
-- @correct_*Smtlib@: No Cryptol spec as of yet.
--
-- @correct_eq@\/@correct_testBit@\/@correct_bitbounds@\/
-- @correct_select@\/@correct_scale_eq@: Haskell-only helpers.
--
-- @correct_asXorDomain@\/@correct_fromXorDomain@: overall-domain \<-\> XOR
-- conversions on @BVDomain@.  Cryptol has no unified @BVDomain@ type (see
-- #401), so the per-subdomain transfer predicates (@correct_arithToXorDomain@,
-- @correct_bitwiseToXorDomain@, @correct_xorToBitwiseDomain@) already cover
-- this ground.
--
-- @precise_overlap@: again, no @BVDomain@, see #401.
--
-- @correct_equiv_*Abstract@: equivalence between the optimized
-- Haskell shift-by-domain impl and its reference spec; the Cryptol
-- side has a single declarative implementation so there's nothing to
-- compare against.
haskellOnly :: Set.Set Text
haskellOnly = Set.fromList
  [ "correct_udivSmtlib", "correct_uremSmtlib"
  , "correct_sdivSmtlib", "correct_sremSmtlib"
  , "correct_eq", "correct_testBit", "correct_bitbounds"
  , "correct_select", "correct_scale_eq"
  , "correct_asXorDomain", "correct_fromXorDomain"
  , "precise_overlap"
  , "correct_equiv_shlAbstract", "correct_equiv_lshrAbstract"
  , "correct_equiv_ashrAbstract"
  , "correct_equiv_rolAbstract", "correct_equiv_rorAbstract"
  -- 'toList' enumerates a CLP's elements; the natural specification is an
  -- unbounded list, which Cryptol's fixed-size sequences can't represent
  -- directly. The 'memberBottom' Cryptol property already pins down 'member'
  -- on the bottom case, so the toList round-trips are Haskell-only.
  , "toListMember", "memberToList"
  ]

cryptolCorrespondenceTests :: TT.TestTree
cryptolCorrespondenceTests = TT.testGroup "Cryptol <-> Haskell"
  [ TT.testGroup "Cryptol predicates have Haskell counterparts"
      [ testCase f (checkCryptolFile f) | f <- cryptolFiles ]
  , TT.testGroup "Haskell predicates have Cryptol counterparts"
      [ testCase (hsModFile m) (checkHaskellFile m) | m <- allHsModules ]
  ]

checkCryptolFile :: FilePath -> Assertion
checkCryptolFile f = do
  cryptolSrc <- TIO.readFile f
  hsNames <-
    fmap Set.unions $ 
      forM allHsModules $ \path -> do
        content <- TIO.readFile (hsModFile path)
        pure (Set.fromList (extractHsPredicates content))
  let cryptolNames = extractCryPredicates cryptolSrc
  assertNonEmpty f "Property" cryptolNames
  let missing = [ cn | cn <- cryptolNames
                     , not (Set.member cn cryptolOnly)
                     , not (Set.member cn hsNames)
                     ]
  case missing of
    [] -> pure ()
    _  -> assertFailure $ T.unpack $ T.unlines $
            ("Cryptol predicates in " <> T.pack f
             <> " with no matching Haskell counterpart:")
            : map ("  " <>) missing

checkHaskellFile :: HsModule -> Assertion
checkHaskellFile m = do
  hsSrc <- TIO.readFile (hsModFile m)
  cryNames <-
    fmap Set.unions $ 
      forM cryptolFiles $ \path -> do
        content <- TIO.readFile path
        pure (Set.fromList (extractCryPredicates content))
  let hsNames = extractHsPredicates hsSrc
  assertNonEmpty (hsModFile m) "Property" hsNames
  let missing = [ hn | hn <- hsNames
                     , not (Set.member hn haskellOnly)
                     , not (Set.member hn cryNames)
                     ]
  case missing of
    [] -> pure ()
    _  -> assertFailure $ T.unpack $ T.unlines $
            ("Haskell predicates in " <> T.pack (hsModFile m)
             <> " with no matching Cryptol counterpart in doc/*.cry:")
            : map ("  " <>) missing

------------------------------------------------------------------------
-- Source extraction

-- | Extract names of top-level @Property@-returning predicates from a Haskell
-- source file.
extractHsPredicates :: Text -> [Text]
extractHsPredicates = extractPredicates "::"

-- | Extract names of top-level @Property@-returning predicates from a Cryptol
-- source file.
extractCryPredicates :: Text -> [Text]
extractCryPredicates = extractPredicates ":"

-- | Extract all top-level predicates whose return type is @Property@ from a
-- source file. The signature operator (@\"::\"@ for Haskell, @\":\"@ for
-- Cryptol) is passed in. Multi-line signatures (where the body continues on
-- indented lines) are collapsed before matching the trailing return type.
extractPredicates :: Text -> Text -> [Text]
extractPredicates sigOp src =
  Set.toAscList . Set.fromList $ go (T.lines src)
  where
    go [] = []
    go (l : rest)
      | Just (nm, restOfLine) <- splitSig sigOp l
      , let (continuation, rest') = span isContinuation rest
            collapsed = T.unwords (restOfLine : map T.stripStart continuation)
      , trailingTokenIs "Property" collapsed
      = nm : go rest'
      | otherwise = go rest

    -- A continuation of a signature: indented and non-blank.
    isContinuation l = case T.uncons l of
      Just (c, _) -> c == ' ' || c == '\t'
      Nothing     -> False

-- | If @line@ begins with an identifier followed by @sigOp@ (e.g.
-- @\"::\"@), return the identifier and the rest of the line after the
-- operator. Otherwise 'Nothing'.
splitSig :: Text -> Text -> Maybe (Text, Text)
splitSig sigOp line
  | not (T.null nm)
  , Just rest' <- T.stripPrefix sigOp (T.stripStart rest)
  = Just (nm, rest')
  | otherwise = Nothing
  where
    (nm, rest) = T.span isIdentChar line

-- | True if the last whitespace-separated token of @s@ equals @tok@.
trailingTokenIs :: Text -> Text -> Bool
trailingTokenIs tok s = case reverse (T.words s) of
  []      -> False
  (w : _) -> w == tok

isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c == '_' || c == '\''

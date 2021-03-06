------------------------------------------------------------------------
-- |
-- Module           : What4.Utils.StringLiteral
-- Description      : Utility definitions for strings
-- Copyright        : (c) Galois, Inc 2019-2020
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

module What4.Utils.StringLiteral
( StringLiteral(..)
, stringLiteralInfo
, fromUnicodeLit
, fromChar8Lit
, fromChar16Lit
, stringLitEmpty
, stringLitLength
, stringLitNull
, stringLitBounds
, stringLitContains
, stringLitIsPrefixOf
, stringLitIsSuffixOf
, stringLitSubstring
, stringLitIndexOf
) where


import           Data.Kind
import           Data.Parameterized.Classes
import qualified Data.ByteString as BS
import           Data.String
import qualified Data.Text as T

import           What4.BaseTypes
import qualified What4.Utils.Word16String as WS


------------------------------------------------------------------------
-- String literals

data StringLiteral (si::StringInfo) :: Type where
  UnicodeLiteral :: !T.Text -> StringLiteral Unicode
  Char8Literal   :: !BS.ByteString -> StringLiteral Char8
  Char16Literal  :: !WS.Word16String -> StringLiteral Char16

stringLiteralInfo :: StringLiteral si -> StringInfoRepr si
stringLiteralInfo UnicodeLiteral{} = UnicodeRepr
stringLiteralInfo Char16Literal{}  = Char16Repr
stringLiteralInfo Char8Literal{}   = Char8Repr

fromUnicodeLit :: StringLiteral Unicode -> T.Text
fromUnicodeLit (UnicodeLiteral x) = x

fromChar8Lit :: StringLiteral Char8 -> BS.ByteString
fromChar8Lit (Char8Literal x) = x

fromChar16Lit :: StringLiteral Char16 -> WS.Word16String
fromChar16Lit (Char16Literal x) = x

instance TestEquality StringLiteral where
  testEquality (UnicodeLiteral x) (UnicodeLiteral y) =
    if x == y then Just Refl else Nothing
  testEquality (Char16Literal x) (Char16Literal y) =
    if x == y then Just Refl else Nothing
  testEquality (Char8Literal x) (Char8Literal y) =
    if x == y then Just Refl else Nothing

  testEquality _ _ = Nothing

instance Eq (StringLiteral si) where
  x == y = isJust (testEquality x y)

instance OrdF StringLiteral where
  compareF (UnicodeLiteral x) (UnicodeLiteral y) =
    case compare x y of
      LT -> LTF
      EQ -> EQF
      GT -> GTF
  compareF UnicodeLiteral{} _ = LTF
  compareF _ UnicodeLiteral{} = GTF

  compareF (Char16Literal x) (Char16Literal y) =
    case compare x y of
      LT -> LTF
      EQ -> EQF
      GT -> GTF
  compareF Char16Literal{} _ = LTF
  compareF _ Char16Literal{} = GTF

  compareF (Char8Literal x) (Char8Literal y) =
    case compare x y of
      LT -> LTF
      EQ -> EQF
      GT -> GTF

instance Ord (StringLiteral si) where
  compare x y = toOrdering (compareF x y)

instance ShowF StringLiteral where
  showF (UnicodeLiteral x) = show x
  showF (Char16Literal x) = show x
  showF (Char8Literal x) = show x

instance Show (StringLiteral si) where
  show = showF


instance HashableF StringLiteral where
  hashWithSaltF s (UnicodeLiteral x) = hashWithSalt (hashWithSalt s (1::Int)) x
  hashWithSaltF s (Char16Literal x)  = hashWithSalt (hashWithSalt s (2::Int)) x
  hashWithSaltF s (Char8Literal x)   = hashWithSalt (hashWithSalt s (3::Int)) x

instance Hashable (StringLiteral si) where
  hashWithSalt = hashWithSaltF

stringLitLength :: StringLiteral si -> Integer
stringLitLength (UnicodeLiteral x) = toInteger (T.length x)
stringLitLength (Char16Literal x)  = toInteger (WS.length x)
stringLitLength (Char8Literal x)   = toInteger (BS.length x)

stringLitEmpty :: StringInfoRepr si -> StringLiteral si
stringLitEmpty UnicodeRepr = UnicodeLiteral mempty
stringLitEmpty Char16Repr  = Char16Literal mempty
stringLitEmpty Char8Repr   = Char8Literal mempty

stringLitNull :: StringLiteral si -> Bool
stringLitNull (UnicodeLiteral x) = T.null x
stringLitNull (Char16Literal x)  = WS.null x
stringLitNull (Char8Literal x)   = BS.null x

stringLitContains :: StringLiteral si -> StringLiteral si -> Bool
stringLitContains (UnicodeLiteral x) (UnicodeLiteral y) = T.isInfixOf y x
stringLitContains (Char16Literal x) (Char16Literal y) = WS.isInfixOf y x
stringLitContains (Char8Literal x) (Char8Literal y) = BS.isInfixOf y x

stringLitIsPrefixOf :: StringLiteral si -> StringLiteral si -> Bool
stringLitIsPrefixOf (UnicodeLiteral x) (UnicodeLiteral y) = T.isPrefixOf x y
stringLitIsPrefixOf (Char16Literal x) (Char16Literal y) = WS.isPrefixOf x y
stringLitIsPrefixOf (Char8Literal x) (Char8Literal y) = BS.isPrefixOf x y

stringLitIsSuffixOf :: StringLiteral si -> StringLiteral si -> Bool
stringLitIsSuffixOf (UnicodeLiteral x) (UnicodeLiteral y) = T.isSuffixOf x y
stringLitIsSuffixOf (Char16Literal x) (Char16Literal y) = WS.isSuffixOf x y
stringLitIsSuffixOf (Char8Literal x) (Char8Literal y) = BS.isSuffixOf x y

stringLitSubstring :: StringLiteral si -> Integer -> Integer -> StringLiteral si
stringLitSubstring (UnicodeLiteral x) len off
  | off < 0 || len < 0 = UnicodeLiteral T.empty
  | otherwise = UnicodeLiteral $ T.take (fromInteger len)  $ T.drop (fromInteger off) x
stringLitSubstring (Char16Literal x) len off
  | off < 0 || len < 0 = Char16Literal WS.empty
  | otherwise = Char16Literal $ WS.take (fromInteger len) $ WS.drop (fromInteger off) x
stringLitSubstring (Char8Literal x) len off
  | off < 0 || len < 0 = Char8Literal BS.empty
  | otherwise = Char8Literal $ BS.take (fromIntegral len) $ BS.drop (fromInteger off) x

-- | Index of first occurrence of second string in first one starting at
--   the position specified by the third argument.
--   @stringLitIndexOf s t k@, with @0 <= k <= |s|@ is the position of the first
--   occurrence of @t@ in @s@ at or after position @k@, if any.
--   Otherwise, it is @-1@. Note that the result is @k@ whenever @k@ is within
--   the range @[0, |s|]@ and @t@ is empty.
stringLitIndexOf :: StringLiteral si -> StringLiteral si -> Integer -> Integer
stringLitIndexOf (UnicodeLiteral x) (UnicodeLiteral y) k
   | k < 0    = -1
   | k > toInteger (T.length x) = -1
   | T.null y = k
   | T.null b = -1
   | otherwise = toInteger (T.length a) + k
  where (a,b) = T.breakOn y (T.drop (fromInteger k) x)

stringLitIndexOf (Char16Literal x) (Char16Literal y) k
  | k < 0 = -1
  | k > toInteger (WS.length x) = -1
  | WS.null y = k
  | otherwise =
      case WS.findSubstring y (WS.drop (fromInteger k) x) of
        Nothing -> -1
        Just n  -> toInteger n + k

stringLitIndexOf (Char8Literal x) (Char8Literal y) k
  | k < 0 = -1
  | k > toInteger (BS.length x) = -1
  | BS.null y = k
  | otherwise =
      case bsFindSubstring y (BS.drop (fromInteger k) x) of
        Nothing -> -1
        Just n  -> toInteger n + k

-- | Get the first index of a substring in another string,
--   or 'Nothing' if the string is not found.
--
--   Copy/pasted from the old `bytestring` implementation because it was
--   deprecated/removed for some reason.
bsFindSubstring :: BS.ByteString -- ^ String to search for.
              -> BS.ByteString -- ^ String to seach in.
              -> Maybe Int
bsFindSubstring pat src
    | BS.null pat && BS.null src = Just 0
    | BS.null b = Nothing
    | otherwise = Just (BS.length a)
  where (a, b) = BS.breakSubstring pat src

stringLitBounds :: StringLiteral si -> Maybe (Int, Int)
stringLitBounds si =
  case si of
    UnicodeLiteral t -> T.foldl' f Nothing t
    Char16Literal ws -> WS.foldl' f Nothing ws
    Char8Literal bs  -> BS.foldl' f Nothing bs

 where
 f :: Enum a =>  Maybe (Int,Int) -> a -> Maybe (Int, Int)
 f Nothing c = Just (fromEnum c, fromEnum c)
 f (Just (lo, hi)) c = lo' `seq` hi' `seq` Just (lo',hi')
    where
    lo' = min lo (fromEnum c)
    hi' = max hi (fromEnum c)


instance Semigroup (StringLiteral si) where
  UnicodeLiteral x <> UnicodeLiteral y = UnicodeLiteral (x <> y)
  Char16Literal x  <> Char16Literal y  = Char16Literal (x <> y)
  Char8Literal x   <> Char8Literal y   = Char8Literal (x <> y)

instance IsString (StringLiteral Unicode) where
  fromString = UnicodeLiteral . T.pack

------------------------------------------------------------------------
-- |
-- Module           : What4.Utils.Word16String
-- Description      : Utility definitions for wide (2-byte) strings
-- Copyright        : (c) Galois, Inc 2019-2020
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

module What4.Utils.Word16String
( Word16String
, fromLEByteString
, toLEByteString
, empty
, singleton
, null
, index
, drop
, take
, append
, length
-- Qualify this name to disambiguate it from the Prelude version of foldl'
-- (defined in base-4.20 or later).
, What4.Utils.Word16String.foldl'
, findSubstring
, isInfixOf
, isPrefixOf
, isSuffixOf
) where

import           Prelude hiding (null,length, drop, take)
import qualified Prelude

import           Data.Bits
import           Data.Char
import           Data.Hashable
import qualified Data.List as List
import           Data.Maybe (isJust)
import           Data.Word
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import           Numeric

-- | A string of Word16 values, encoded as a bytestring
--   in little endian (LE) order.
--
--   We maintain the invariant that Word16Strings
--   are represented by an even number of bytes.
newtype Word16String = Word16String ByteString


instance Semigroup Word16String where
  (<>) = append

instance Monoid Word16String where
  mempty = empty

instance Eq Word16String where
  (Word16String xs) == (Word16String ys) = xs == ys

instance Ord Word16String where
  compare (Word16String xs) (Word16String ys) = compare xs ys

instance Show Word16String where
 showsPrec _ = showsWord16String

instance Hashable Word16String where
 hashWithSalt s (Word16String xs) = hashWithSalt s xs

showsWord16String :: Word16String -> ShowS
showsWord16String (Word16String xs0) tl = '"' : go (BS.unpack xs0)
 where
 go [] = '"' : tl
 go (_:[]) = error "showsWord16String: representation has odd number of bytes!"
 go (lo:hi:xs)
    | c == '"'    = "\\\"" ++ go xs
    | isPrint c   = c : go xs
    | otherwise   = "\\u" ++ zs ++ esc ++ go xs

  where
  esc = showHex x []
  zs  = Prelude.take (4 - Prelude.length esc) (repeat '0')

  x :: Word16
  x = fromIntegral lo .|. (fromIntegral hi `shiftL` 8)

  c :: Char
  c = toEnum (fromIntegral x)


-- | Generate a @Word16String@ from a bytestring
--   where the 16bit words are encoded as two bytes
--   in little-endian order.
--
--   PRECONDITION: the input bytestring must
--   have a length which is a multiple of 2.
fromLEByteString :: ByteString -> Word16String
fromLEByteString xs
  | BS.length xs `mod` 2 == 0 = Word16String xs
  | otherwise = error "fromLEByteString: bytestring must have even length"

-- | Return the underlying little endian bytestring.
toLEByteString :: Word16String -> ByteString
toLEByteString (Word16String xs) = xs

-- | Return the empty string
empty :: Word16String
empty = Word16String BS.empty

-- | Compute the string containing just the given character
singleton :: Word16 -> Word16String
singleton c = Word16String (BS.pack [ lo , hi ])
 where
 lo, hi :: Word8
 lo = fromIntegral (c .&. 0xFF)
 hi = fromIntegral (c `shiftR` 8)

-- | Test if the given string is empty
null :: Word16String -> Bool
null (Word16String xs) = BS.null xs

-- | Retrive the @n@th character of the string.
--   Out of bounds accesses will cause an error.
index :: Word16String -> Int -> Word16
index (Word16String xs) i = (hi `shiftL` 8) .|. lo
 where
 lo, hi :: Word16
 hi = fromIntegral (BS.index xs (2*i + 1))
 lo = fromIntegral (BS.index xs (2*i))

drop :: Int -> Word16String -> Word16String
drop k (Word16String xs) = Word16String (BS.drop (2*k) xs)

take :: Int -> Word16String -> Word16String
take k (Word16String xs) = Word16String (BS.take (2*k) xs)

append :: Word16String -> Word16String -> Word16String
append (Word16String xs) (Word16String ys) =
  Word16String (BS.append xs ys)

length :: Word16String -> Int
length (Word16String xs) = BS.length xs `shiftR` 1

foldl' :: (a -> Word16 -> a) -> a -> Word16String -> a
foldl' f z xs =
  List.foldl' (\x i -> f x (index xs i)) z [ 0 .. (length xs - 1) ]

-- | Find the first index (if it exists) where the first
--   string appears as a substring in the second
findSubstring :: Word16String -> Word16String -> Maybe Int
findSubstring (Word16String xs) _ | BS.null xs = Just 0
findSubstring (Word16String xs) (Word16String ys) = go 0
  where
  brk = BS.breakSubstring xs

  -- search for the first aligned (even) index where the pattern string occurs
  -- invariant: k is even
  go k
    | BS.null b = Nothing
    | even (BS.length a) = Just ((k + BS.length a) `shiftR` 1)
    | otherwise = go (k + BS.length a + 1)
   where
   (a,b) = brk (BS.drop k ys)

-- | Returns true if the first string appears somewhere
--   in the second string.
isInfixOf :: Word16String -> Word16String -> Bool
isInfixOf xs ys = isJust $ findSubstring xs ys

isPrefixOf :: Word16String -> Word16String -> Bool
isPrefixOf (Word16String xs) (Word16String ys) = BS.isPrefixOf xs ys

isSuffixOf :: Word16String -> Word16String -> Bool
isSuffixOf (Word16String xs) (Word16String ys) = BS.isSuffixOf xs ys

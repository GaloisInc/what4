------------------------------------------------------------------------
-- |
-- Module           : What4.Utils.Streams
-- Description      : IO stream utilities
-- Copyright        : (c) Galois, Inc 2013-2020
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------
module What4.Utils.Streams
( logErrorStream
) where

import           Data.ByteString (ByteString)
import           Data.Text (unpack)
import           Data.Text.Encoding (decodeUtf8With)
import           Data.Text.Encoding.Error (lenientDecode)
import qualified System.IO.Streams as Streams

-- | Write from input stream to a logging function.
logErrorStream :: Streams.InputStream ByteString
               -> (String -> IO ()) -- ^ Logging function
               -> IO ()
logErrorStream err_stream logFn = do
  -- Have err_stream log complete lines to logLn
  let write_err Nothing = return ()
      write_err (Just b) = logFn b
  err_output <- Streams.makeOutputStream write_err
  lns <- Streams.map (unpack . decodeUtf8With lenientDecode) =<< Streams.lines err_stream
  Streams.connect lns err_output

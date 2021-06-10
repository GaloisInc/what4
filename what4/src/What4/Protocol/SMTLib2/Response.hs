{-|
This module defines types and operations for parsing SMTLib2 solver responses.

These are high-level responses, as describe in
@https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf@,
page 47, Figure 3.9.

This parser is designed to be the top level handling for solver
responses, and to be used in conjuction with
What4.Protocol.SMTLib2.Parse and What4.Protocol.SExp with the latter
handling detailed parsing of specific constructs returned in the body
of the general response.
-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module What4.Protocol.SMTLib2.Response
  (
    SMTResponse(..)
  , SMTLib2Exception(..)
  , getSolverResponse
  , getLimitedSolverResponse
  , smtParseOptions
  , strictSMTParsing
  , strictSMTParseOpt
  )
where

import           Control.Applicative
import           Control.Exception
import qualified Data.Attoparsec.Text as AT
import           Data.Maybe ( isJust )
import           Data.Text ( Text )
import qualified Data.Text as Text
import qualified Data.Text.Lazy as Lazy
import qualified Data.Text.Lazy.Builder as Builder
import qualified Prettyprinter.Util as PPU
import qualified System.IO.Streams as Streams
import qualified System.IO.Streams.Attoparsec.Text as AStreams

import qualified What4.BaseTypes as BT
import qualified What4.Config as CFG
import           What4.Protocol.SExp
import qualified What4.Protocol.SMTLib2.Syntax as SMT2
import qualified What4.Protocol.SMTWriter as SMTWriter
import           What4.Utils.Process ( filterAsync )


strictSMTParsing :: CFG.ConfigOption BT.BaseBoolType
strictSMTParsing = CFG.configOption BT.BaseBoolRepr "solver.strict_parsing"

strictSMTParseOpt :: CFG.ConfigDesc
strictSMTParseOpt =
  CFG.mkOpt strictSMTParsing CFG.boolOptSty
  (Just $ PPU.reflow $
   Text.concat ["Strictly parse SMT responses and fail on"
               , "unrecognized data (the default)."
               , "This might need to be disabled when running"
               , "the SMT solver in verbose mode."
               ])
  Nothing

smtParseOptions :: [CFG.ConfigDesc]
smtParseOptions = [ strictSMTParseOpt ]


data SMTResponse = AckSuccess
                 | AckUnsupported
                 | AckError Text
                 | AckSat
                 | AckUnsat
                 | AckUnknown
                 | RspName Text
                 | RspVersion Text
                 | RspErrBehavior Text
                 | RspOutOfMemory
                 | RspRsnIncomplete
                 | RspUnkReason SExp
                 | AckSuccessSExp SExp
                 | AckSkipped Text SMTResponse
                 deriving (Eq, Show)

-- | Called to get a response from the SMT connection.

getSolverResponse :: SMTWriter.WriterConn t h
                  -> IO (Either SomeException SMTResponse)
getSolverResponse conn = do
  mb <- tryJust filterAsync
        (AStreams.parseFromStream
          -- n.b. the parseFromStream with an attoparsec parser used
          -- here will throw
          -- System.IO.Streams.Attoparsec.ParseException on a parser
          -- failure; the rspParser throws some other parse errors
          (rspParser (SMTWriter.strictParsing conn))
          (SMTWriter.connInputHandle conn))
  return mb


-- | Gets a limited set of responses, throwing an exception when a
-- response is not matched by the filter.  Also throws exceptions for
-- standard error results.  The passed command and intent arguments
-- are only used for marking error messages.
--
-- Callers which do not want exceptions thrown for standard error
-- conditions should feel free to use 'getSolverResponse' and handle
-- all response cases themselves.

getLimitedSolverResponse :: String
                         -> (SMTResponse -> Maybe a)
                         -> SMTWriter.WriterConn t h
                         -> SMT2.Command
                         -> IO a
getLimitedSolverResponse intent handleResponse conn cmd =
  let validateResp rsp =
        case rsp of
          AckUnsupported -> throw (SMTLib2Unsupported cmd)
          (AckError msg) -> throw (SMTLib2Error cmd msg)
          (AckSkipped _line rest) -> validateResp rest
          _ -> case handleResponse rsp of
                 Just x -> return x
                 Nothing -> throw $ SMTLib2InvalidResponse cmd intent rsp
  in getSolverResponse conn >>= \case
    Right rsp -> validateResp rsp
    Left se@(SomeException e)
      | isJust $ filterAsync se -> throw e
      | Just (AStreams.ParseException _) <- fromException se
        -> do -- Parser failed and left the unparseable input in the
              -- stream; extract it to show the user
              curInp <- Streams.read (SMTWriter.connInputHandle conn)
              throw $ SMTLib2ParseError intent [cmd] $ Text.pack $
                unlines [ "Solver response parsing failure."
                        , "*** Exception: " ++ displayException e
                        , "Attempting to parse input for " <> intent <> ":"
                        , show curInp
                        ]
      | otherwise -> throw e



rspParser :: SMTWriter.ResponseStrictness -> AT.Parser SMTResponse
rspParser strictness =
  let lexeme p = skipSpaceOrNewline *> p
      parens p = AT.char '(' *> p <* AT.char ')'
      errParser = parens $ lexeme (AT.string "error")
                  *> (AckError <$> lexeme parseSMTLib2String)
      specific_success_response = check_sat_response <|> get_info_response
      check_sat_response = (AckSat <$ AT.string "sat")
                           <|> (AckUnsat <$ AT.string "unsat")
                           <|> (AckUnknown <$ AT.string "unknown")
      get_info_response = parens info_response
      info_response = errBhvParser
                      <|> nameParser
                      <|> unkReasonParser
                      <|> versionParser
      nameParser = lexeme (AT.string ":name")
                   *> lexeme (RspName <$> parseSMTLib2String)
      versionParser = lexeme (AT.string ":version")
                      *> lexeme (RspVersion <$> parseSMTLib2String)
      errBhvParser = lexeme (AT.string ":error-behavior")
                     *> lexeme (RspErrBehavior <$>
                                (AT.string "continued-execution"
                                 <|> AT.string "immediate-exit")
                                 -- Explicit error instead of generic
                                 -- fallback since :error-behavior was
                                 -- matched but behavior type was not.
                                 <|> throw (SMTLib2ResponseUnrecognized
                                            SMT2.getErrorBehavior
                                            "bad :error-behavior value")
                               )
      unkReasonParser =
        lexeme (AT.string ":reason-unknown")
        *> lexeme (RspOutOfMemory <$ AT.string "memout"
                    <|> RspRsnIncomplete <$ AT.string "incomplete"
                    <|> (AT.char '(' *> (RspUnkReason <$> parseSExpBody parseSMTLib2String))
                    -- already matched :reason-unknown, so any other
                    -- arguments to that are errors.
                    <|> throw (SMTLib2ResponseUnrecognized
                               (SMT2.Cmd "reason?")
                               "bad :reason-unknown value")
                  )
  in skipSpaceOrNewline *>
     ((AckSuccess <$ AT.string "success")
      <|> (AckUnsupported <$ AT.string "unsupported")
      <|> specific_success_response
      <|> errParser
      <|> (AT.char '(' *> (AckSuccessSExp <$> parseSExpBody parseSMTLib2String))
      -- sometimes verbose output mode will generate interim text
      -- before the actual ack; the following skips lines of input
      -- that aren't recognized.
       <|> (case strictness of
              SMTWriter.Strict -> empty
              SMTWriter.Lenient -> AckSkipped
                                   <$> AT.takeWhile1 (not . AT.isEndOfLine)
                                   <*> (rspParser strictness))
     )

parseSMTLib2String :: AT.Parser Text
parseSMTLib2String = AT.char '\"' >> go
 where
 go :: AT.Parser Text
 go = do xs <- AT.takeWhile (not . (=='\"'))
         _ <- AT.char '\"'
         (do _ <- AT.char '\"'
             ys <- go
             return (xs <> "\"" <> ys)
          ) <|> return xs

----------------------------------------------------------------------

data SMTLib2Exception
  = SMTLib2Unsupported SMT2.Command
  | SMTLib2Error SMT2.Command Text
  | SMTLib2ParseError SMTLib2Intent [SMT2.Command] Text
  | SMTLib2ResponseUnrecognized SMT2.Command Text
  | SMTLib2InvalidResponse SMT2.Command SMTLib2Intent SMTResponse

type SMTLib2Intent = String

instance Show SMTLib2Exception where
  show =
    let showCmd (SMT2.Cmd c) = Lazy.unpack $ Builder.toLazyText c
    in unlines . \case
      (SMTLib2Unsupported cmd) ->
        [ "unsupported command:"
        , "  " <> showCmd cmd
        ]
      (SMTLib2Error cmd msg) ->
        [ "Solver reported an error:"
        , "  " ++ Text.unpack msg
        , "in response to command:"
        , "  " <> showCmd cmd
        ]
      (SMTLib2ParseError intent cmds msg) ->
        [ "Could not parse solver response:"
        , "  " ++ Text.unpack msg
        , "in response to commands for " <> intent <> ":"
        ] ++ map showCmd cmds
      (SMTLib2ResponseUnrecognized cmd rsp) ->
        [ "Unrecognized response from solver:"
        , "  " <> Text.unpack rsp
        , "in response to command:"
        , "  " <> showCmd cmd
        ]
      (SMTLib2InvalidResponse cmd intent rsp) ->
        [ "Received parsed and understood but unexpected response from solver:"
        , "  " <> show rsp
        , "in response to command for " <> intent <> ":"
        , "  " <> showCmd cmd
        ]

instance Exception SMTLib2Exception

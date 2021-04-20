{- |
Module      : What4.Protocol.Online
Description : Online solver interactions
Copyright   : (c) Galois, Inc 2018-2020
License     : BSD3
Maintainer  : Rob Dockins <rdockins@galois.com>

This module defines an API for interacting with
solvers that support online interaction modes.

-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module What4.Protocol.Online
  ( OnlineSolver(..)
  , AnOnlineSolver(..)
  , SolverProcess(..)
  , SolverGoalTimeout(..)
  , getGoalTimeoutInSeconds
  , ErrorBehavior(..)
  , killSolver
  , push
  , pop
  , reset
  , inNewFrame
  , inNewFrameWithVars
  , check
  , checkAndGetModel
  , checkWithAssumptions
  , checkWithAssumptionsAndModel
  , getModel
  , getUnsatCore
  , getUnsatAssumptions
  , getSatResult
  , checkSatisfiable
  , checkSatisfiableWithModel
  ) where

import           Control.Exception
                   ( SomeException(..), catchJust, tryJust, displayException )
import           Control.Monad ( unless )
import           Control.Monad (void, forM, forM_)
import           Control.Monad.Catch ( MonadMask, bracket_, onException )
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import           Data.Parameterized.Some
import           Data.Proxy
import           Data.IORef
import           Data.Text (Text)
import qualified Data.Text.Lazy as LazyText
import           Prettyprinter
import           System.Exit
import           System.IO
import qualified System.IO.Streams as Streams
import           System.Process
                   (ProcessHandle, terminateProcess, waitForProcess)

import           What4.Expr
import           What4.Interface (SolverEvent(..)
                                 , SolverStartSATQuery(..)
                                 , SolverEndSATQuery(..) )
import           What4.ProblemFeatures
import           What4.Protocol.SMTWriter
import           What4.SatResult
import           What4.Utils.HandleReader
import           What4.Utils.Process (filterAsync)


-- | Simple data-type encapsulating some implementation
--   of an online solver.
data AnOnlineSolver = forall s. OnlineSolver s => AnOnlineSolver (Proxy s)

-- | This class provides an API for starting and shutting down
--   connections to various different solvers that support
--   online interaction modes.
class SMTReadWriter solver => OnlineSolver solver where
  -- | Start a new solver process attached to the given `ExprBuilder`.
  startSolverProcess :: forall scope st fs.
    ProblemFeatures ->
    Maybe Handle ->
    ExprBuilder scope st fs ->
    IO (SolverProcess scope solver)

  -- | Shut down a solver process.  The process will be asked to shut down in
  --   a "polite" way, e.g., by sending an `(exit)` message, or by closing
  --   the process's `stdin`.  Use `killProcess` instead to shutdown a process
  --   via a signal.
  shutdownSolverProcess :: forall scope.
    SolverProcess scope solver ->
    IO (ExitCode, LazyText.Text)

-- | This datatype describes how a solver will behave following an error.
data ErrorBehavior
  = ImmediateExit -- ^ This indicates the solver will immediately exit following an error
  | ContinueOnError
     -- ^ This indicates the solver will remain live and respond to further
     --   commmands following an error

-- | The amount of time that a solver is allowed to attempt to satisfy
-- any particular goal.
--
-- The timeout value may be retrieved with
-- 'getGoalTimeoutInMilliSeconds' or 'getGoalTimeoutInSeconds'.
newtype SolverGoalTimeout = SolverGoalTimeout { getGoalTimeoutInMilliSeconds :: Integer }

-- | Get the SolverGoalTimeout raw numeric value in units of seconds.
getGoalTimeoutInSeconds :: SolverGoalTimeout -> Integer
getGoalTimeoutInSeconds sgt =
  let msecs = getGoalTimeoutInMilliSeconds sgt
      secs = msecs `div` 1000
      -- 0 is a special "no-timeout" value, so if the supplied goal
      -- timeout in milliseconds is less than one second, round up to
      -- a full second.
  in if msecs > 0 && secs == 0 then 1 else secs


-- | A live connection to a running solver process.
--
--   This data structure should be used in a single-threaded
--   manner or with external synchronization to ensure that
--   only a single thread has access at a time. Unsynchronized
--   multithreaded use will lead to race conditions and very
--   strange results.
data SolverProcess scope solver = SolverProcess
  { solverConn  :: !(WriterConn scope solver)
    -- ^ Writer for sending commands to the solver

  , solverCleanupCallback :: IO ExitCode
    -- ^ Callback for regular code paths to gracefully close associated pipes
    --   and wait for the process to shutdown

  , solverHandle :: !ProcessHandle
    -- ^ Handle to the solver process

  , solverStdin :: !(Streams.OutputStream Text)
    -- ^ Standard in for the solver process.

  , solverResponse :: !(Streams.InputStream Text)
    -- ^ Wrap the solver's stdout, for easier parsing of responses.

  , solverErrorBehavior :: !ErrorBehavior
    -- ^ Indicate this solver's behavior following an error response

  , solverStderr :: !HandleReader
    -- ^ Standard error for the solver process

  , solverEvalFuns :: !(SMTEvalFunctions solver)
    -- ^ The functions used to parse values out of models.

  , solverLogFn :: SolverEvent -> IO ()

  , solverName :: String

  , solverEarlyUnsat :: IORef (Maybe Int)
    -- ^ Some solvers will enter an 'UNSAT' state early, if they can easily
    --   determine that context is unsatisfiable.  If this IORef contains
    --   an integer value, it indicates how many \"pop\" operations need to
    --   be performed to return to a potentially satisfiable state.
    --   A @Just 0@ state indicates the special case that the top-level context
    --   is unsatisfiable, and must be \"reset\".

  , solverSupportsResetAssertions :: Bool
    -- ^ Some solvers do not have support for the SMTLib2.6 operation
    --   (reset-assertions), or an equivalent.
    --   For these solvers, we instead make sure to
    --   always have at least one assertion frame pushed, and pop all
    --   outstanding frames (and push a new top-level one) as a way
    --   to mimic the reset behavior.

  , solverGoalTimeout :: SolverGoalTimeout
    -- ^ The amount of time (in seconds) that a solver should spend
    -- trying to satisfy any particular goal before giving up.  A
    -- value of zero indicates no time limit.
  }


-- | An impolite way to shut down a solver.  Prefer to use
--   `shutdownSolverProcess`, unless the solver is unresponsive
--   or in some unrecoverable error state.
killSolver :: SolverProcess t solver -> IO ()
killSolver p =
  do catchJust filterAsync
           (terminateProcess (solverHandle p))
           (\(ex :: SomeException) -> hPutStrLn stderr $ displayException ex)
     void $ waitForProcess (solverHandle p)

-- | Check if the given formula is satisfiable in the current
--   solver state, without requesting a model.  This is done in a
--   fresh frame, which is exited after the check call.
checkSatisfiable ::
  SMTReadWriter solver =>
  SolverProcess scope solver ->
  String ->
  BoolExpr scope ->
  IO (SatResult () ())
checkSatisfiable proc rsn p =
  readIORef (solverEarlyUnsat proc) >>= \case
    Just _  -> return (Unsat ())
    Nothing ->
      let conn = solverConn proc in
      inNewFrame proc $
        do assume conn p
           check proc rsn

-- | Check if the formula is satisifiable in the current
--   solver state.  This is done in a
--   fresh frame, which is exited after the continuation
--   complets. The evaluation function can be used to query the model.
--   The model is valid only in the given continuation.
checkSatisfiableWithModel ::
  SMTReadWriter solver =>
  SolverProcess scope solver ->
  String ->
  BoolExpr scope ->
  (SatResult (GroundEvalFn scope) () -> IO a) ->
  IO a
checkSatisfiableWithModel proc rsn p k =
  readIORef (solverEarlyUnsat proc) >>= \case
    Just _  -> k (Unsat ())
    Nothing ->
      let conn = solverConn proc in
      inNewFrame proc $
        do assume conn p
           checkAndGetModel proc rsn >>= k

--------------------------------------------------------------------------------
-- Basic solver interaction.

-- | Pop all assumption frames and remove all top-level
--   asserts from the global scope.  Forget all declarations
--   except those in scope at the top level.
reset :: SMTReadWriter solver => SolverProcess scope solver -> IO ()
reset p =
  do let c = solverConn p
     n <- popEntryStackToTop c
     writeIORef (solverEarlyUnsat p) Nothing
     if solverSupportsResetAssertions p then
       addCommand c (resetCommand c)
     else
       do mapM_ (addCommand c) (popManyCommands c n)
          addCommand c (pushCommand c)

-- | Push a new solver assumption frame.
push :: SMTReadWriter solver => SolverProcess scope solver -> IO ()
push p =
  readIORef (solverEarlyUnsat p) >>= \case
    Nothing -> do let c = solverConn p
                  pushEntryStack c
                  addCommand c (pushCommand c)
    Just i  -> writeIORef (solverEarlyUnsat p) $! (Just $! i+1)

-- | Pop a previous solver assumption frame.
pop :: SMTReadWriter solver => SolverProcess scope solver -> IO ()
pop p =
  readIORef (solverEarlyUnsat p) >>= \case
    Nothing -> do let c = solverConn p
                  popEntryStack c
                  addCommand c (popCommand c)
    Just i
      | i <= 1 -> do let c = solverConn p
                     popEntryStack c
                     writeIORef (solverEarlyUnsat p) Nothing
                     addCommand c (popCommand c)
      | otherwise -> writeIORef (solverEarlyUnsat p) $! (Just $! i-1)

-- | Pop a previous solver assumption frame, but don't communicate
--   the pop command to the solver.  This is really only useful in
--   error recovery code when we know the solver has already exited.
popStackOnly :: SolverProcess scope solver -> IO ()
popStackOnly p =
  readIORef (solverEarlyUnsat p) >>= \case
    Nothing -> do let c = solverConn p
                  popEntryStack c
    Just i
      | i <= 1 -> do let c = solverConn p
                     popEntryStack c
                     writeIORef (solverEarlyUnsat p) Nothing
      | otherwise -> writeIORef (solverEarlyUnsat p) $! (Just $! i-1)


-- | Perform an action in the scope of a solver assumption frame.
inNewFrame :: (MonadIO m, MonadMask m, SMTReadWriter solver) => SolverProcess scope solver -> m a -> m a
inNewFrame p action = inNewFrameWithVars p [] action

-- | Perform an action in the scope of a solver assumption frame, where the given
-- bound variables are considered free within that frame.
inNewFrameWithVars :: (MonadIO m, MonadMask m, SMTReadWriter solver)
                   => SolverProcess scope solver
                   -> [Some (ExprBoundVar scope)]
                   -> m a
                   -> m a
inNewFrameWithVars p vars action =
  case solverErrorBehavior p of
    ContinueOnError ->
      bracket_ (liftIO $ pushWithVars)
               (liftIO $ pop p)
               action
    ImmediateExit ->
      do liftIO $ pushWithVars
         x <- (onException action (liftIO $ popStackOnly p))
         liftIO $ pop p
         return x
  where
    conn = solverConn p
    pushWithVars = do
      push p
      forM_ vars (\(Some bv) -> bindVarAsFree conn bv)

checkWithAssumptions ::
  SMTReadWriter solver =>
  SolverProcess scope solver ->
  String ->
  [BoolExpr scope] ->
  IO ([Text], SatResult () ())
checkWithAssumptions proc rsn ps =
  do let conn = solverConn proc
     readIORef (solverEarlyUnsat proc) >>= \case
       Just _  -> return ([], Unsat ())
       Nothing ->
         do tms <- forM ps (mkFormula conn)
            nms <- forM tms (freshBoundVarName conn EqualityDefinition [] BoolTypeMap)
            solverLogFn proc
              (SolverStartSATQuery $ SolverStartSATQueryRec
              { satQuerySolverName = solverName proc
              , satQueryReason = rsn
              })
            addCommands conn (checkWithAssumptionsCommands conn nms)
            sat_result <- getSatResult proc
            solverLogFn proc
              (SolverEndSATQuery $ SolverEndSATQueryRec
              { satQueryResult = sat_result
              , satQueryError = Nothing
              })
            return (nms, sat_result)

checkWithAssumptionsAndModel ::
  SMTReadWriter solver =>
  SolverProcess scope solver ->
  String ->
  [BoolExpr scope] ->
  IO (SatResult (GroundEvalFn scope) ())
checkWithAssumptionsAndModel proc rsn ps =
  do (_nms, sat_result) <- checkWithAssumptions proc rsn ps
     case sat_result of
       Unknown -> return Unknown
       Unsat x -> return (Unsat x)
       Sat{} -> Sat <$> getModel proc

-- | Send a check command to the solver, and get the SatResult without asking
--   a model.
check :: SMTReadWriter solver => SolverProcess scope solver -> String -> IO (SatResult () ())
check p rsn =
  readIORef (solverEarlyUnsat p) >>= \case
    Just _  -> return (Unsat ())
    Nothing ->
      do let c = solverConn p
         solverLogFn p
           (SolverStartSATQuery $ SolverStartSATQueryRec
           { satQuerySolverName = solverName p
           , satQueryReason = rsn
           })
         addCommands c (checkCommands c)
         sat_result <- getSatResult p
         solverLogFn p
           (SolverEndSATQuery $ SolverEndSATQueryRec
           { satQueryResult = sat_result
           , satQueryError = Nothing
           })
         return sat_result

-- | Send a check command to the solver and get the model in the case of a SAT result.
checkAndGetModel :: SMTReadWriter solver => SolverProcess scope solver -> String -> IO (SatResult (GroundEvalFn scope) ())
checkAndGetModel yp rsn = do
  sat_result <- check yp rsn
  case sat_result of
    Unsat x -> return $! Unsat x
    Unknown -> return Unknown
    Sat () -> Sat <$> getModel yp

-- | Following a successful check-sat command, build a ground evaulation function
--   that will evaluate terms in the context of the current model.
getModel :: SMTReadWriter solver => SolverProcess scope solver -> IO (GroundEvalFn scope)
getModel p = smtExprGroundEvalFn (solverConn p)
             $ smtEvalFuns (solverConn p) (solverResponse p)

-- | After an unsatisfiable check-with-assumptions command, compute a set of the supplied
--   assumptions that (together with previous assertions) form an unsatisfiable core.
--   Note: the returned unsatisfiable set might not be minimal.  The boolean value
--   returned along with the name indicates if the assumption was negated or not:
--   @True@ indidcates a positive atom, and @False@ represents a negated atom.
getUnsatAssumptions :: SMTReadWriter solver => SolverProcess scope solver -> IO [(Bool,Text)]
getUnsatAssumptions proc =
  do let conn = solverConn proc
     unless (supportedFeatures conn `hasProblemFeature` useUnsatAssumptions) $
       fail $ show $ pretty (smtWriterName conn) <+> pretty "is not configured to produce UNSAT assumption lists"
     addCommandNoAck conn (getUnsatAssumptionsCommand conn)
     smtUnsatAssumptionsResult conn (solverResponse proc)

-- | After an unsatisfiable check-sat command, compute a set of the named assertions
--   that (together with all the unnamed assertions) form an unsatisfiable core.
--   Note: the returned unsatisfiable core might not be minimal.
getUnsatCore :: SMTReadWriter solver => SolverProcess scope solver -> IO [Text]
getUnsatCore proc =
  do let conn = solverConn proc
     unless (supportedFeatures conn `hasProblemFeature` useUnsatCores) $
       fail $ show $ pretty (smtWriterName conn) <+> pretty "is not configured to produce UNSAT cores"
     addCommandNoAck conn (getUnsatCoreCommand conn)
     smtUnsatCoreResult conn (solverResponse proc)

-- | Get the sat result from a previous SAT command.
getSatResult :: SMTReadWriter s => SolverProcess t s -> IO (SatResult () ())
getSatResult yp = do
  let ph = solverHandle yp
  sat_result <- tryJust filterAsync (smtSatResult yp (solverResponse yp))
  case sat_result of
    Right ok -> return ok

    Left (SomeException e) ->
       do -- Interrupt process
          terminateProcess ph

          txt <- readAllLines $ solverStderr yp

          -- Wait for process to end
          ec <- waitForProcess ph
          let ec_code = case ec of
                          ExitSuccess -> 0
                          ExitFailure code -> code
          fail $ unlines
                  [ "The solver terminated with exit code "++
                                              show ec_code ++ ".\n"
                  , "*** exception: " ++ displayException e
                  , "*** standard error:"
                  , LazyText.unpack txt
                  ]

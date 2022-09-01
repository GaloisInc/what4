{-# LANGUAGE CPP #-}
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
  , solverStdin
  , solverResponse
  , SolverGoalTimeout(..)
  , getGoalTimeoutInSeconds
  , withLocalGoalTimeout
  , ErrorBehavior(..)
  , killSolver
  , push
  , pop
  , tryPop
  , reset
  , inNewFrame
  , inNewFrameWithVars
  , inNewFrame2Open
  , inNewFrame2Close
  , check
  , checkAndGetModel
  , checkWithAssumptions
  , checkWithAssumptionsAndModel
  , getModel
  , getUnsatCore
  , getAbducts
  , getUnsatAssumptions
  , getSatResult
  , checkSatisfiable
  , checkSatisfiableWithModel
  ) where

import           Control.Concurrent ( threadDelay )
import           Control.Concurrent.Async ( race )
import           Control.Exception ( SomeException(..), catchJust, tryJust, displayException )
import           Control.Monad ( unless )
import           Control.Monad (void, forM, forM_)
import           Control.Monad.Catch ( Exception, MonadMask, bracket_, catchIf
                                     , onException, throwM, fromException  )
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import           Data.IORef
#if MIN_VERSION_base(4,14,0)
#else
import qualified Data.List as L
#endif
import           Data.Parameterized.Some
import           Data.Proxy
import           Data.Text (Text)
import qualified Data.Text.Lazy as LazyText
import           Prettyprinter
import           System.Exit
import           System.IO
import qualified System.IO.Error as IOE
import qualified System.IO.Streams as Streams
import           System.Process (ProcessHandle, terminateProcess, waitForProcess)

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

instance Pretty SolverGoalTimeout where
  pretty (SolverGoalTimeout ms) = pretty ms <> pretty "msec"

instance Show SolverGoalTimeout where
  show = show . pretty

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
    --
    -- Note that it is not sufficient to set just this value to
    -- control timeouts; this value is used as a reference for common
    -- code (e.g. SMTLIB2) to determine the timeout for the associated
    -- timer.  When initialized, this field of the SolverProcess is
    -- initialized from a solver-specific timeout configuration
    -- (e.g. z3Timeout); the latter is the definitive reference for
    -- the timeout, and solver-specific code will likely use the the
    -- latter rather than this common field.
  }


-- | Standard input stream for the solver process.
solverStdin :: (SolverProcess t solver) -> (Streams.OutputStream Text)
solverStdin = connHandle . solverConn

-- | The solver's stdout, for easier parsing of responses.
solverResponse :: (SolverProcess t solver) -> (Streams.InputStream Text)
solverResponse = connInputHandle . solverConn


-- | An impolite way to shut down a solver.  Prefer to use
--   `shutdownSolverProcess`, unless the solver is unresponsive
--   or in some unrecoverable error state.
killSolver :: SolverProcess t solver -> IO ()
killSolver p =
  do catchJust filterAsync
           (terminateProcess (solverHandle p)
            -- some solvers emit stderr messages on SIGTERM
            >> readAllLines (solverStderr p)
            >> return ()
           )
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

-- | @get-abuct nm t@ queries the solver for the first abduct, which is returned
--   as an SMT function definition named @nm@. The remaining abducts are obtained
--   from the solver by successive invocations of the @get-abduct-next@ command,
--   which return SMT functions bound to the same @nm@ as the first. The name @nm@
--   is bound within the current assertion frame.
--   Note that this is an unstable API; we expect that the return type will change 
--   to a parsed expression in the future
getAbducts ::
  SMTReadWriter solver =>
  SolverProcess scope solver ->
  Int ->
  Text ->
  BoolExpr scope ->
  IO [String]
getAbducts proc n nm t =
  if (n > 0) then do 
    let conn = solverConn proc
    unless (supportedFeatures conn `hasProblemFeature` useProduceAbducts) $
      fail $ show $ pretty (smtWriterName conn) <+> pretty "is not configured to produce abducts"
    f <- mkFormula conn t
    -- get the first abduct using the get-abduct command
    addCommandNoAck conn (getAbductCommand conn nm f)
    abd1 <- smtAbductResult conn conn nm f
    -- get the remaining abducts using get-abduct-next commands
    if (n > 1) then do
      let rest = n - 1
      abdRest <- forM [1..rest] $ \_ -> do
        addCommandNoAck conn (getAbductNextCommand conn)
        smtAbductNextResult conn conn
      return (abd1:abdRest)
    else return [abd1]
  else return []

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

-- | Pop a previous solver assumption frame, but allow this to fail if
-- the solver has exited.
tryPop :: SMTReadWriter solver => SolverProcess scope solver -> IO ()
tryPop p =
  let trycmd conn = catchIf solverGone
                    (addCommand conn (popCommand conn))
                    (const $ throwM RunawaySolverTimeout)
#if MIN_VERSION_base(4,14,0)
      solverGone = IOE.isResourceVanishedError
#else
      solverGone = L.isInfixOf "resource vanished" . IOE.ioeGetErrorString
#endif
  in readIORef (solverEarlyUnsat p) >>= \case
    Nothing -> do let c = solverConn p
                  popEntryStack c
                  trycmd c
    Just i
      | i <= 1 -> do let c = solverConn p
                     popEntryStack c
                     writeIORef (solverEarlyUnsat p) Nothing
                     trycmd c
      | otherwise -> writeIORef (solverEarlyUnsat p) $! (Just $! i-1)




-- | Perform an action in the scope of a solver assumption frame.
inNewFrame :: (MonadIO m, MonadMask m, SMTReadWriter solver) => SolverProcess scope solver -> m a -> m a
inNewFrame p action = inNewFrameWithVars p [] action

-- | Open a second solver assumption frame.
-- For abduction, we want the final assertion to be a in a new frame, so that it 
-- can be closed before asking for abducts. The following two commands allow frame 2 
-- to be pushed and popped independently of other commands
inNewFrame2Open :: SMTReadWriter solver => SolverProcess scope solver -> IO ()
inNewFrame2Open sp = let c = solverConn sp in addCommand c (push2Command c)

-- | Close a second solver assumption frame.
inNewFrame2Close :: SMTReadWriter solver => SolverProcess scope solver -> IO ()
inNewFrame2Close sp = let c = solverConn sp in addCommand c (pop2Command c)

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
               (liftIO $ tryPop p)
               action
    ImmediateExit ->
      do liftIO $ pushWithVars
         onException (do x <- action
                         liftIO $ pop p
                         return x
                     )
           (liftIO $ tryPop p)
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

-- | Following a successful check-sat command, build a ground evaluation function
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
     smtUnsatAssumptionsResult conn conn

-- | After an unsatisfiable check-sat command, compute a set of the named assertions
--   that (together with all the unnamed assertions) form an unsatisfiable core.
--   Note: the returned unsatisfiable core might not be minimal.
getUnsatCore :: SMTReadWriter solver => SolverProcess scope solver -> IO [Text]
getUnsatCore proc =
  do let conn = solverConn proc
     unless (supportedFeatures conn `hasProblemFeature` useUnsatCores) $
       fail $ show $ pretty (smtWriterName conn) <+> pretty "is not configured to produce UNSAT cores"
     addCommandNoAck conn (getUnsatCoreCommand conn)
     smtUnsatCoreResult conn conn

-- | Get the sat result from a previous SAT command.
getSatResult :: SMTReadWriter s => SolverProcess t s -> IO (SatResult () ())
getSatResult yp = do
  let ph = solverHandle yp
  let action = smtSatResult yp
  sat_result <- withLocalGoalTimeout yp action

  case sat_result of
    Right ok -> return ok

    Left e@(SomeException _)
      | Just RunawaySolverTimeout <- fromException e -> do
          -- Deadman timeout fired, so this is effectively Incomplete
          return Unknown

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


-- | If the solver cannot voluntarily limit itself to the requested
-- timeout period, this runs a local async process with a slightly
-- longer time period that will forcibly terminate the solver process
-- if it expires while the solver process is still running.
--
-- Note that this will require re-establishment of the solver process
-- and any associated context for any subsequent solver goal
-- evaluation.

withLocalGoalTimeout ::
  SolverProcess t s
  -> (WriterConn t s -> IO (SatResult () ()))
  -> IO (Either SomeException (SatResult () ()))
withLocalGoalTimeout solverProc action =
  if getGoalTimeoutInSeconds (solverGoalTimeout solverProc) == 0
  then do tryJust filterAsync (action $ solverConn solverProc)
  else let deadmanTimeoutPeriodMicroSeconds =
             (fromInteger $
              getGoalTimeoutInMilliSeconds (solverGoalTimeout solverProc)
              + 500  -- allow solver to honor timeout first
             ) * 1000  -- convert msec to usec
           deadmanTimer = threadDelay deadmanTimeoutPeriodMicroSeconds
       in
          do race deadmanTimer (action $ solverConn solverProc) >>= \case
               Left () -> do killSolver solverProc
                             return $ Left $ SomeException RunawaySolverTimeout
               Right x -> return $ Right x


-- | The RunawaySolverTimeout is thrown when the solver cannot
-- voluntarily limit itself to the requested solver-timeout period and
-- has subsequently been forcibly stopped.
data RunawaySolverTimeout = RunawaySolverTimeout deriving Show
instance Exception RunawaySolverTimeout

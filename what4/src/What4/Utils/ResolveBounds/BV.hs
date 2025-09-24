{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

{-|
Module           : What4.Utils.ResolveBounds.BV
Description      : Resolve the lower and upper bounds of a SymBV
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Ryan Scott <rscott@galois.com>

A utility for using an 'WPO.OnlineSolver' to query if a 'WI.SymBV' is concrete
or symbolic, and if it is symbolic, what the lower and upper bounds are.
-}
module What4.Utils.ResolveBounds.BV
  ( resolveSymBV
  , SearchStrategy(..)
  , ResolvedSymBV(..)
  ) where

import           Data.BitVector.Sized ( BV )
import qualified Data.BitVector.Sized as BV
import qualified Data.Parameterized.NatRepr as PN
import qualified Prettyprinter as PP

import qualified What4.Expr.Builder as WEB
import qualified What4.Expr.GroundEval as WEG
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.Protocol.SMTWriter as WPS
import qualified What4.SatResult as WSat
import qualified What4.Utils.BVDomain.Arith as WUBA

-- | The results of an 'WPO.OnlineSolver' trying to resolve a 'WI.SymBV' as
-- concrete.
data ResolvedSymBV w
  = BVConcrete (BV w)
    -- ^ A concrete bitvector, including its value as a 'BV'.
  | BVSymbolic (WUBA.Domain w)
    -- ^ A symbolic 'SymBV', including its lower and upper bounds as a
    --   'WUBA.Domain'.

instance Show (ResolvedSymBV w) where
  showsPrec _p res =
    case res of
      BVConcrete bv ->
        showString "BVConcrete " . showsPrec 11 bv
      BVSymbolic d  ->
        let (lb, ub) = WUBA.ubounds d in
          showString "BVSymbolic ["
        . showsPrec 11 lb
        . showString ", "
        . showsPrec 11 ub
        . showString "]"

-- | The strategy to use to search for lower and upper bounds in
-- 'resolveSymBV'.
data SearchStrategy
  = ExponentialSearch
    -- ^ After making an initial guess for a bound, increase (for upper bounds)
    --   or decrease (for lower bounds) the initial guess by an exponentially
    --   increasing amount (1, 2, 4, 8, ...) until the bound has been exceeded.
    --   At that point, back off from exponential search and use binary search
    --   until the bound has been determined.
    --
    --   For many use cases, this is a reasonable default.
  | BinarySearch
    -- ^ Use binary search to found each bound, using @0@ as the leftmost
    --   bounds of the search and 'BV.maxUnsigned' as the rightmost bounds of
    --   the search.

  -- Some possibilities for additional search strategies include:
  --
  -- - Using Z3's minimize/maximize commands. See
  --   https://github.com/GaloisInc/what4/issues/188
  --
  -- - A custom, user-specified strategy that uses callback(s) to guide the
  --   search at each iteration.

instance PP.Pretty SearchStrategy where
  pretty ExponentialSearch = PP.pretty "exponential search"
  pretty BinarySearch      = PP.pretty "binary search"

-- | Use an 'WPO.OnlineSolver' to attempt to resolve a 'WI.SymBV' as concrete.
-- If it cannot, return the lower and upper bounds. This is primarly intended
-- for compound expressions whose bounds cannot trivially be determined by
-- using 'WI.signedBVBounds' or 'WI.unsignedBVBounds'.
--
-- For just resolving a bitvector as concrete without searching for bounds, see
-- 'What4.Concretize.uniquelyConcretize'.
resolveSymBV ::
     forall w sym solver scope st fs
   . ( 1 PN.<= w
     , sym ~ WEB.ExprBuilder scope st fs
     , WPO.OnlineSolver solver
     )
  => sym
  -> SearchStrategy
     -- ^ The strategy to use when searching for lower and upper bounds. For
     --   many use cases, 'ExponentialSearch' is a reasonable default.
  -> PN.NatRepr w
     -- ^ The bitvector width
  -> WPO.SolverProcess scope solver
     -- ^ The online solver process to use to search for lower and upper
     --   bounds.
  -> WI.SymBV sym w
     -- ^ The bitvector to resolve.
  -> IO (ResolvedSymBV w)
resolveSymBV sym searchStrat w proc symBV =
  -- First check, if the SymBV can be trivially resolved as concrete. If so,
  -- this can avoid the need to call out to the solver at all.
  case WI.asBV symBV of
    Just bv -> pure $ BVConcrete bv
    -- Otherwise, we need to consult the solver.
    Nothing -> do
      -- First, ask for a particular model of the SymBV...
      modelForBV <- WPO.inNewFrame proc $ do
        msat <- WPO.checkAndGetModel proc "resolveSymBV (check with initial assumptions)"
        model <- case msat of
          WSat.Unknown   -> failUnknown
          WSat.Unsat{}   -> fail "resolveSymBV: Initial assumptions are unsatisfiable"
          WSat.Sat model -> pure model
        WEG.groundEval model symBV
      -- ...next, check if this is the only possible model for this SymBV. We
      -- do this by adding a blocking clause that assumes the SymBV is /not/
      -- equal to the model we found in the previous step. If this is
      -- unsatisfiable, the SymBV can only be equal to that model, so we can
      -- conclude it is concrete. If it is satisfiable, on the other hand, the
      -- SymBV can be multiple values, so it is truly symbolic.
      isSymbolic <- WPO.inNewFrame proc $ do
        block <- WI.notPred sym =<< WI.bvEq sym symBV =<< WI.bvLit sym w modelForBV
        WPS.assume conn block
        msat <- WPO.check proc "resolveSymBV (check under assumption that model cannot happen)"
        case msat of
          WSat.Unknown -> failUnknown
          WSat.Sat{}   -> pure True  -- Truly symbolic
          WSat.Unsat{} -> pure False -- Concrete
      if isSymbolic
        then
          -- If we have a truly symbolic SymBV, search for its lower and upper
          -- bounds, using the model from the previous step as a starting point
          -- for the search.
          case searchStrat of
            ExponentialSearch -> do
              -- Use the model from the previous step as the initial guess for
              -- each bound
              lowerBound <- computeLowerBoundExponential modelForBV
              upperBound <- computeUpperBoundExponential modelForBV
              pure $ BVSymbolic $ WUBA.range w
                (BV.asUnsigned lowerBound) (BV.asUnsigned upperBound)
            BinarySearch -> do
              lowerBound <- computeLowerBoundBinary bvZero bvMaxUnsigned
              upperBound <- computeUpperBoundBinary bvZero bvMaxUnsigned
              pure $ BVSymbolic $ WUBA.range w
                (BV.asUnsigned lowerBound) (BV.asUnsigned upperBound)
        else pure $ BVConcrete modelForBV
  where
    conn :: WPS.WriterConn scope solver
    conn = WPO.solverConn proc

    failUnknown :: forall a. IO a
    failUnknown = fail "resolveSymBV: Resolving value yielded UNKNOWN"

    bvZero :: BV w
    bvZero = BV.zero w

    bvOne :: BV w
    bvOne = BV.one w

    bvTwo :: BV w
    bvTwo = BV.mkBV w 2

    bvMaxUnsigned :: BV w
    bvMaxUnsigned = BV.maxUnsigned w

    -- The general strategy for finding a bound is that we start searching
    -- from a particular value known to be within bounds. At each step, we
    -- change this value by exponentially increasing amount, then check if we
    -- have exceeded the bound by using the solver. If so, we then fall back to
    -- binary search to determine an exact bound. If we are within bounds, we
    -- repeat the process.
    --
    -- As an example, let's suppose we having a symbolic value with bounds of
    -- [0, 12], and we start searching for the upper bound at the value 1:
    --
    -- * In the first step, we add 1 to the starting value to get 2. We check
    --   if two has exceeded the upper bound using the solver. This is not the
    --   case, so we continue.
    -- * In the second step, we add 2 to the starting value. The result, 3,
    --   is within bounds.
    -- * We continue like this in the third and fourth steps, except that
    --   we add 4 and 8 to the starting value to get 5 and 9, respectively.
    -- * In the fifth step, we add 16 to the starting value. The result, 17,
    --   has exceeded the upper bound. We will now fall back to binary search,
    --   using the previous result (9) as the leftmost bounds of the search and
    --   the current result (17) as the rightmost bounds of the search.
    -- * Eventually, binary search discovers that 12 is the upper bound.
    --
    -- Note that at each step, we must also check to make sure that the amount
    -- to increase the starting value by does not cause a numeric overflow. If
    -- this would be the case, we fall back to binary search, using
    -- BV.maxUnsigned as the rightmost bounds of the search.
    --
    -- The process for finding a lower bound is quite similar, except that we
    -- /subtract/ an exponentially increasing amount from the starting value
    -- each time rather than adding it.

    computeLowerBoundExponential :: BV w -> IO (BV w)
    computeLowerBoundExponential start = go start bvOne
      where
        go :: BV w -> BV w -> IO (BV w)
        go previouslyTried diff
          | -- If the diff is larger than the starting value, then subtracting
            -- the diff from the starting value would cause underflow. Instead,
            -- just fall back to binary search, using 0 as the leftmost bounds
            -- of the search.
            start `BV.ult` diff
          = computeLowerBoundBinary bvZero previouslyTried

          | -- Otherwise, check if (start - diff) exceeds the lower bound for
            -- the symBV.
            otherwise
          = do let nextToTry = BV.sub w start diff
               exceedsLB <- checkExceedsLowerBound nextToTry
               if |  -- If we have exceeded the lower bound, fall back to
                     -- binary search.
                     exceedsLB
                  -> computeLowerBoundBinary nextToTry previouslyTried
                  |  -- Make sure that (diff * 2) doesn't overflow. If it
                     -- would, fall back to binary search.
                     BV.asUnsigned diff * 2 > BV.asUnsigned bvMaxUnsigned
                  -> computeLowerBoundBinary bvZero nextToTry
                  |  -- Otherwise, keep exponentially searching.
                     otherwise
                  -> go nextToTry $ BV.mul w diff bvTwo

    -- Search for the upper bound of the SymBV. This function assumes the
    -- following invariants:
    --
    -- * l <= r
    --
    -- * The lower bound of the SymBV is somewhere within the range [l, r].
    computeLowerBoundBinary :: BV w -> BV w -> IO (BV w)
    computeLowerBoundBinary l r
      | -- If the leftmost and rightmost bounds are the same, we are done.
        l == r
      = pure l

      | -- If the leftmost and rightmost bounds of the search are 1 apart, we
        -- only have two possible choices for the lower bound. Consult the
        -- solver to determine which one is the lower bound.
        BV.sub w r l < bvTwo
      = do lExceedsLB <- checkExceedsLowerBound l
           pure $ if lExceedsLB then r else l

      | -- Otherwise, keep binary searching.
        otherwise
      = do let nextToTry = BV.mkBV w ((BV.asUnsigned l + BV.asUnsigned r) `div` 2)
           exceedsLB <- checkExceedsLowerBound nextToTry
           if exceedsLB
             then computeLowerBoundBinary nextToTry r
             else computeLowerBoundBinary l nextToTry

    checkExceedsLowerBound :: BV w -> IO Bool
    checkExceedsLowerBound bv = WPO.inNewFrame proc $ do
      leLowerBound <- WI.bvUle sym symBV =<< WI.bvLit sym w bv
      WPS.assume conn leLowerBound
      msat <- WPO.check proc "resolveSymBV (check if lower bound has been exceeded)"
      case msat of
        WSat.Unknown -> failUnknown
        WSat.Sat{}   -> pure False
        WSat.Unsat{} -> pure True -- symBV cannot be <= this value,
                                  -- so the value must be strictly
                                  -- less than the lower bound.

    computeUpperBoundExponential :: BV w -> IO (BV w)
    computeUpperBoundExponential start = go start bvOne
      where
        go :: BV w -> BV w -> IO (BV w)
        go previouslyTried diff
          | -- Make sure that adding the diff to the starting value will not
            -- result in overflow. If it would, just fall back to binary
            -- search, using BV.maxUnsigned as the rightmost bounds of the
            -- search.
            BV.asUnsigned start + BV.asUnsigned diff > BV.asUnsigned bvMaxUnsigned
          = computeUpperBoundBinary previouslyTried bvMaxUnsigned

          | otherwise
          = do let nextToTry = BV.add w start diff
               exceedsUB <- checkExceedsUpperBound nextToTry
               if |  -- If we have exceeded the upper bound, fall back to
                     -- binary search.
                     exceedsUB
                  -> computeUpperBoundBinary previouslyTried nextToTry
                  |  -- Make sure that (diff * 2) doesn't overflow. If it
                     -- would, fall back to binary search.
                     BV.asUnsigned diff * 2 > BV.asUnsigned bvMaxUnsigned
                  -> computeUpperBoundBinary nextToTry bvMaxUnsigned
                  |  -- Otherwise, keep exponentially searching.
                     otherwise
                  -> go nextToTry $ BV.mul w diff bvTwo

    -- Search for the upper bound of the SymBV. This function assumes the
    -- following invariants:
    --
    -- * l <= r
    --
    -- * The upper bound of the SymBV is somewhere within the range [l, r].
    computeUpperBoundBinary :: BV w -> BV w -> IO (BV w)
    computeUpperBoundBinary l r
      | -- If the leftmost and rightmost bounds are the same, we are done.
        l == r
      = pure l

      | -- If the leftmost and rightmost bounds of the search are 1 apart, we
        -- only have two possible choices for the upper bound. Consult the
        -- solver to determine which one is the upper bound.
        BV.sub w r l < bvTwo
      = do rExceedsUB <- checkExceedsUpperBound r
           pure $ if rExceedsUB then l else r

      | -- Otherwise, keep binary searching.
        otherwise
      = do let nextToTry = BV.mkBV w ((BV.asUnsigned l + BV.asUnsigned r) `div` 2)
           exceedsUB <- checkExceedsUpperBound nextToTry
           if exceedsUB
             then computeUpperBoundBinary l nextToTry
             else computeUpperBoundBinary nextToTry r

    checkExceedsUpperBound :: BV w -> IO Bool
    checkExceedsUpperBound bv = WPO.inNewFrame proc $ do
      geUpperBound <- WI.bvUge sym symBV =<< WI.bvLit sym w bv
      WPS.assume conn geUpperBound
      msat <- WPO.check proc "resolveSymBV (check if upper bound has been exceeded)"
      case msat of
        WSat.Unknown -> failUnknown
        WSat.Sat{}   -> pure False
        WSat.Unsat{} -> pure True -- symBV cannot be >= this upper bound,
                                  -- so the value must be strictly
                                  -- greater than the upper bound.

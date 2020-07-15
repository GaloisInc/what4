{-# LANGUAGE Trustworthy, TemplateHaskell #-}
module What4.Panic
  (HasCallStack, What4, Panic, panic) where

import Panic hiding (panic)
import qualified Panic

data What4 = What4

-- | `panic` represents an error condition that should only
--   arise due to a programming error. It will exit the program
--   and print a message asking users to open a ticket.
panic :: HasCallStack =>
  String {- ^ Short name of where the error occured -} ->
  [String] {- ^ More detailed description of the error  -} ->
  a
panic = Panic.panic What4

instance PanicComponent What4 where
  panicComponentName _ = "What4"
  panicComponentIssues _ = "https://github.com/GaloisInc/what4/issues"

  {-# Noinline panicComponentRevision #-}
  panicComponentRevision = $useGitRevision

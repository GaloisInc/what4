# Overview of What4

What4 provides a language to represent symbolic computations and the
ability to perform those computations using one of several SMT
solvers, including Yices, Z3, CVC4, and others.

## What4 Language

The What4 language is also referred to as the "solver interface".  It
is the in-memory representation of a symbolic formula that will be
sent to the solver.

The What4.Interface defines the classes that specify the various
solver expression operators and terms, along with associated data
objects defining the useable solver types and utilities such as
statistics and value conversion.

The `What4.Expr.Builder` provides the canonical instance of the classes
defined in `What4.Interface`, and is the module that is commonly used by
code that is generating a symbolic expression to be solved.

The `What4.Interface` is parameterized by a `sym` type, which represents
the specific solver that will be used to evaluate the symbolic formula
once it has been defined.

## Running Solvers

Most online solvers are run as subprocesses, with the main process
interacting with the subprocess via the stdin/stdout of that
subprocess.

Each solver has different characteristics and interactions; these
solver-specific details are handled by a solver-specific component in
the src/What4/Solver directory.  This includes the creation of an
active connection to the solver.  The `src/What4/Solver.hs` file
provides the general API interacting with solvers in a generic
fashion.

Interaction with the solver is primarily managed by the code in the
`src/What4/Protocol` directory, which will utilize solver-specific
code as needed.

### Solver process management

The `src/What4/Utils/Process.hs` provides the core set of functions used
to start and stop solver processes.

A solver connection is typically a long-running process and
corresponding set of pipes over which communications can occur.  The
What4/Protocol code manages the connection, including initiating the
creation of a solver subprocess as needed if the previous process exits.

Interaction with most solvers uses the SMTLIB2 interface, which is a
standard interface supported by many solvers which participate in the
SMT benchmarking challenge.  Solvers may provide alternative
interfaces as well.


#### Signals (Ctrl-C)

There is no explicit management of signals or `Ctrl-C` provided by
What4.

The normal system support for `Ctrl-C` is to generate a `SIGINT` signal
(or `CTRL_C_EVENT/CTRL_BREAK_EVENT` on Windows) to all processes in
the foreground group.  Typically the foreground group includes the
main process running the What4 code and any solvers that have been
started.

What4 itself does not install any special `SIGINT` handling,
although it does have some `finally` cleanup code.  Normal processing
of a `Ctrl-C` event then is that the solvers will all exit, the
process running the What4 code will run the `finally` cleanup code,
and then exit itself.

Note that the above is only true for the first `Ctrl-C` event.  The
normal GHC runtime configuration is to pass the first `SIGINT` to the
running code (defaulting to an exit if no handlers are provided), but
to immediately terminate the process on the second event (see
https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/rts/signals for
more information).  In the immediate termination case, no cleanup
code is run, although this is still delivered to all foreground
processes, so the expectation is that the solver processes will
receive this and exit.

#### Yices

Yices interaction does not use the `yices_smt2` executable which
provides the SMTLIB2 interface; instead What4 uses the `yices`
executable, which supports the Yices language.

The origins of this difference were likely related to array support
features that weren't available in SMTLIB2, and original development
of the code that is now in What4 may have predated SMTLIB2
availability.

> At the present time (2021), it is thought that SMTLIB2 support for
> Array theory may be sufficiently advanced that the Yices language
> interface is no longer needed, but this requires further
> investigation.

Note that because of the use of the `yices` executable the Yices
solver interaction is a notable exception to the process and signal
management described above.  The `yices` REPL mode modifies `SIGINT`
(`Ctrl-C`) to stop the current search and return to the REPL prompt
and `SIGINT` is otherwise ignored. Thus, use of `Ctrl-C` when running
with the Yices online solver will typically leave behind one or more
`yices` processes that must be manually killed.

While it is possible to install a handler for keyboard interrupts that
will shutdown the Yices process, this is problematic for several
reasons:

1. Different techniques and libraries must be used for Posix/Unix
   v.s. Windows.

2. Installation of the handler disables normal signal handling
   provided by the RTS; extra care must be taken to allow full program
   exit.

3. This internal handling stance may conflict with application-level
   handling of keyboard interrupt handling intentions.

A future version of Yices may provide the ability to specify normal
keyboard interrupt handling via command-line parameters.

#!/usr/bin/env swipl

%% This script is used to generate an output matrix (in JSON format)
%% that the github actions can import and use to generate various test
%% configurations.
%%
%% There are three main axes: os, compiler, and solver.  The os and
%% compiler axis have a vector of versions, one or more of which
%% should be designated as the main version.  The solver axis has a
%% solver version vector for each defined solver, where again at least
%% one of each should be designated as the main solver version.
%%
%% Adding versions or identifiers to any axis is done with a simple
%% declarative statement in the first section below.
%%
%% The output matrix defines a more efficient selection of tests than
%% a full cartesian product (because the latter would uselessly test
%% many redundant configurations).
%%
%%  1. Test the main version of each solver on the code build with the
%%     main version of the compiler, for each operating system
%%     (solver_main_compiler_main).
%%
%%  2. Test the other versions of compiled code with the main version
%%     of each solver, for each operating system
%%     (solver_main_compiler_all).
%%
%%  3. Test the other versions of each solver on the main compiler
%%     version of the code, for each operating system
%%     (solver_all_compiler_main).  Note that the tests run against
%%     each solver independently, but a test run will test all
%%     available solvers (and skip any unavailable solvers), so the
%%     most efficient matrix varies each solver version independently
%%     (but in parallel) for each test run until all solver versions
%%     are exhausted.
%%
%% This script can be run by hand to see the generated JSON output
%% using SWI Prolog:
%%
%%    $ swipl .github/workflows/gen_matrix.pl

:- initialization(main, main).
:- use_module(library(http/json)).
:- use_module(library(clpfd)).

%% Declare every Operating System that should be tested (separately in
%% sequence)
os(ubuntu).

%% Declare every Compiler that should be used to build the code
%% (separately in sequence)
compiler(ghc).

%% Declare every Solver that should be used (in parallel, not in
%% sequence: one version of every solver is chosen for each test.
solver(z3).
solver(yices).
solver(stp).
solver(cvc4).
solver(boolector).
solver(abc).

%% Specify the main version of each variable (i.e. the most
%% interesting value of that variable.  The main version is the one
%% used for builds that are testing other variations; there is no
%% other purpose behind the main_version designation, and there may be
%% multiple main versions for a particular vector but they currently
%% provide no advantage.
%%
%% The main version selected is usually the "most commonly used"
%% version (which is not necessarily the "most recently released"
%% version.
main_version(ubuntu, "ubuntu-latest").
main_version(ghc, "8.10.7").
main_version(z3, "4_8_14").
main_version(yices, "2_6").
main_version(stp, "2_3_3").
main_version(cvc4, "1_8").
main_version(boolector, "3_2_2").
main_version(abc, "2021_12_30").

%% Specify the versions of the operating system(s) to use to build and
%% test the code, the versions of the Haskell compiler to use for
%% building, and the versions of the solvers to use in tests.
%%
%% New versions can be added by simply adding a statement here, and
%% old versions can be removed by deleting the corresponding
%% statement.  There is no significance to ordering and the following
%% can be ordered or grouped in any sequence.

version(ubuntu, "ubuntu-latest").

version(ghc, "9.0.2").
version(ghc, "8.10.7").
version(ghc, "8.8.4").
version(ghc, "8.6.5").

version(z3, "4_8_14").
version(z3, "4_8_13").
version(z3, "4_8_12").
version(z3, "4_8_11").
version(z3, "4_8_10").
version(z3, "4_8_8").
version(z3, "4_8_9").

version(yices, "2_6_1").
version(yices, "2_6").

version(stp, "2_3_3").
version(stp, "2_3_2").
% n.b. stp 2_2_0 fails, no reason to test it

version(cvc4, "1_8").
version(cvc4, "1_7").

version(boolector, "3_2_2").
version(boolector, "3_2_1").
% n.b. boolector 3.1.0 builds fail; no reason to test it

version(abc, "2021_12_30").
version(abc, "2020_06_22").

%% ----------------------------------------------------------------------
%% No changes normally needed below

matrix(Matrix) :-
    findall(M,
            ( solver_main_compiler_main(M)
            ; solver_all_compiler_main(M)
            ; solver_main_compiler_all(M)
            ), FullMatrix),
    Matrix = matrix{ include:FullMatrix }.

main_solvers(Spec) :- findall(X, (solver(S), main_version(S, V) , X=S:V), Spec).

solver_main_compiler_main(MatrixEntry) :-
    main_solvers(Solvers),
    compiler(Compiler),
    main_version(Compiler, CompilerVersion),
    matrix_entry(Compiler, CompilerVersion, Solvers, MatrixEntry).

solver_main_compiler_all(MatrixEntry) :-
    main_solvers(Solvers),
    compiler(Compiler),
    version(Compiler, CompilerVersion),
    \+ main_version(Compiler, CompilerVersion),
    matrix_entry(Compiler, CompilerVersion, Solvers, MatrixEntry).

matrix_entry(Compiler, CompilerVersion, Solvers, MatrixEntry) :-
    os(OS), main_version(OS, OSVersion),
    MatrixEntry = include{ os:OSVersion }
                  .put(Compiler, CompilerVersion)
                  .put(Solvers).


%% Need to check other solver versions.  It would be inefficient to
%% test the cartesian product of solvers and versions because the
%% solvers are used independently (i.e. z3 and yices are independent,
%% so testing z3 4.8.4 only needs to be done once, not once for each
%% version of yices.
%%
%% Also note that the tests will only run the solvers available to
%% them.

solver_alt_versions(Solver, Versions) :-
    findall(V, (solver(Solver),
                version(Solver, V),
                \+ main_version(Solver, V)),
            Versions).

solvers(Solvers) :- findall(S, solver(S), Solvers).

num_solver_versions(Solver, NumVer) :-
    solver_alt_versions(Solver, Vs),
    length(Vs, NumVer).

nth_solver_version(Solver, N, Version) :-
    solver_alt_versions(Solver, Versions),
    (nth0(N, Versions, Version)
     % Disable the following line to include only solvers with new
     % versions.  When enabled, this specifies other solvers at their
     % main_version when there are no more alternate versions.
     , !; main_version(Solver, Version)
    ).

solver_all_compiler_main(MatrixEntry) :-
    solvers(Solvers), !,
    maplist(num_solver_versions, Solvers, Cnt),
    max_list(Cnt, M), L #= M - 1, N in 0..L, indomain(N),
    findall(E,
            (solver(S),
             nth_solver_version(S, N, V),
             E = S:V),
            SolverSpec),
    compiler(Compiler), main_version(Compiler, CompilerVersion),
    matrix_entry(Compiler, CompilerVersion, SolverSpec, MatrixEntry).


main :-
    matrix(Matrix),
    json_write_dict(current_output, Matrix).

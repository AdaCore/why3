:x: marks a potential source of incompatibility

Session
  * file path stored in session files are now represented in an
    system-independent way, so as to work for example under exotic OS
    like MS-windows

Drivers
  * the clause `syntax converter` disappeared. Any former use should
    be replaced by `syntax literal` and/or `syntax function`

Language
  * the `any` expression is now always ghost
  * A syntactic sugar called "auto-dereference" is introduced, so as
    to avoid, on simple programs, the heavy use of `(!)` character on
    references. See details in Section A.1 of the manual.

Transformations
  * `split_vc` and `subst_all` now avoid substituting user symbols by
    generated ones :x:
  * `destruct_rec` applies `destruct` recursively on a goal
  * `destruct` now simplifies away equalities on constructors
  * `destruct_alg` renamed to `destruct_term`. It also has a new experimental
    keyword `using` to name newly destructed elements

Tools
  * added a command `why3 session update` to modify sessions from the
    command line; so far, only option `-rename-file` exists, for
    renaming files
  * `why3 config --add-prover` now takes the shortcut as second
    argument; option `--list-prover-ids` has been renamed to
    `--list-prover-families` :x:

IDE
  * clicking on the status of a failed proof attempt in the proof tree
    now generates counterexamples
  * added support for GTK3

Counterexamples
  * Field names now use ident names instead of smt generated ones:
    int32qtint -> int32'int
  * Fix parsing of bitvector counterexamples orignated from Z3

Provers
  * support for Z3 4.8.1 (released Oct 16, 2018)
  * support for Z3 4.8.3 (released Nov 20, 2018)
  * support for Z3 4.8.4 (released Dec 20, 2018)

Version 1.1.1, December 17, 2018
--------------------------------

Bug fixes
  * prevented broken extraction of `any`
  * fixed evaluation order when extracting nested mutators
  * fixed extraction of nested recursive polymorphic functions
  * fixed cloning of expressions raising exceptions

Version 1.1.0, October 17, 2018
-------------------------------

Core
  * variants can now be inferred on some lemma functions
  * coercions are now supported for `if` and `match` branches
  * `interrupt` command should now properly interrupt running provers.
  * clearer typing error messages thanks to printing qualified names
  * fixed handling of prover upgrades, resurrected the policy
    "duplicate" and added a policy "remove"

API
  * added `Call_provers.interrupt_call` to interrupt a running prover
    (contribution by Pierre-Yves Strub)

Language
  * program functions can now be marked `partial` to prevent them from
    being used in ghost context; the annotation does not have to be
    explicitly put on their callers
  * `use` now accepts several module names separated by commas
  * symbolic operators can be used in identifiers like `(+)_ident` or
    `([])'ident`
  * range types have now a default ordering to be used in `variant` clause

Standard library
  * library `ieee_float`: floating-point operations can now be used in
    programs

Transformations
  * `split_vc` behaves slightly differently :x:

Provers
  * support for Alt-Ergo 2.1.0 (released Mar 14, 2018)
  * support for Alt-Ergo 2.2.0 (released Apr 26, 2018)
  * support for Coq 8.8.1 (released Jun 29, 2018)
  * support for Coq 8.8.2 (released Sep 26, 2018)
  * support for CVC4 1.6 (released Jun 25, 2018)
  * support for Z3 4.7.1 (released May 23, 2018)
  * support for Isabelle 2018 (released Aug 2018)
    (contribution by Stefan Berghofer)
  * dropped support for Isabelle 2016 (2017 still supported) :x:
  * dropped support for Alt-Ergo versions < 2.0.0 :x:

Version 1.0.0, June 25, 2018
----------------------------

Core
  * improved support of counter-examples
  * attribute `[@vc:sp]` on an expression switches from traditional WP
    to Flanagan-Saxe-like VC generation
  * type invariants now produce logical axioms;
    a type with an invariant must be proved to be inhabited :x:
  * logical symbols can no longer be used in non-ghost code;
    in particular, there is no polymorphic equality in programs any more,
    so equality functions must be declared/defined on a per-type basis
    (already done for type `int` in the standard library) :x:

Language
  * numerous changes to syntax, see documentation appendix :x:
  * `let function`, `let predicate`, `val function`, and `val predicate`
    introduce symbols in both logic and programs
  * added overloading of program symbols
  * new contract clause `alias { <term> with <term>, ... }` :x:
  * support for parallel assignment `<term>,... <- <term>,...`
  * support for local exceptions using `exception ... in ...`
  * added `break`, `continue`, and `return` statements
  * support for `exception` branches in `match` constructs
  * support for `for` loops on range types
    (including machine integers from the standard library)
  * support for type coercions in logic using `meta coercion`
  * keyword `theory` is deprecated; use `module` instead
  * term on the left of sequence `;` must be of type `unit` :x:
  * cloned axioms turn into lemmas; use `with axiom my_axiom`
    or `with axiom .` to keep them as axioms :x:
  * `any <type> <spec>` produces an existential precondition;
    use `val f : <type> <spec> in ...` (unsafe!) instead :x:
  * `use T` and `clone T` now import the generated namespace T;
    use `use T as T` and `clone T as T` to prevent this :x:
  * `pure { <term> }` produces a ghost value in program code
  * `a <-> b <-> c` is now parsed as `(a <-> b) /\ (b <-> c)`;
    `a <-> b -> c` is now rejected :x:

Standard library
  * machine integers in `mach.int.*` are now range types :x:
  * added a minimal memory model for the C language in `mach.c`
  * new modules `witness.Witness` and `witness.Nat`

Extraction
  * improved extraction to OCaml
  * added partial extraction to C using the memory model of `mach.c`
  * added extraction to CakeML (using `why3 extract -D cakeml ...`)

Transformations
  * transformations can now have arguments
  * added transformations `assert`, `apply`, `cut`, `rewrite`, etc., à la Coq
  * added transformations for reflection-based proofs

Drivers
  * support for `use` in theory drivers

IDE
  * replaced left toolbar by a contextual menu
  * source is now editable
  * premises are no longer implicitly introduced
  * added textual interface to call transformations and provers

Tools
  * deprecated `.why` file extension; use `.mlw` instead

Provers
  * removed the `why3` Coq tactic :x:
  * dropped support for Coq 8.4 :x:

Miscellaneous
  * moved the opam base package to `why3`; added `why3-ide` and `why3-coq`

Version 0.88.3, January 11, 2018
--------------------------------

Provers
  * support for Alt-Ergo 2.0.0 (released Nov 14, 2017)
  * support for Coq 8.7.1 (released Dec 16, 2017)
  * support for Z3 4.6.0 (released Dec 18, 2017)

Standard library
  * fixed soundness of theory `int.Exponentiation` when multiplication is not
    commutative :x:

Miscellaneous
  * fixed support for `--enable_relocation=yes` (issue #50)
  * fixed support for Windows (issue #70)

Version 0.88.2, December 7, 2017
--------------------------------

Miscellaneous
  * `why3 session html`: improved compliance of generated files
  * `why3 doc`: fixed missing anchors for operator definitions
  * improved build process when `coqtop.byte` is missing

Version 0.88.1, November 6, 2017
--------------------------------

API
  * exported function `Call_provers.get_new_results`

Provers
  * improved support for Isabelle 2017
  * fixed support for Coq 8.7 (released Oct 17, 2017)

Miscellaneous
  * fixed compilation for OCaml 4.06
  * improved support for nullary `val` declarations with regions

Version 0.88.0, October 6, 2017
-------------------------------

Language
  * added two new forms of type declarations: integer range types and
    floating-point types. To denote constants in such types, integer
    constants and real constants can be cast to such types. This
    support is exploited in drivers for provers that support bitvector
    theories (CVC4, Z3) and floating-point theory (Z3).
    More details in the manual, section 7.2.4 "Theories".
  * a quote character `'` inside an identifier must either be at the
    end, or be followed by either a digit, the underscore character
    `_` or another quote. Identifiers with a quote followed by a
    letter are reserved. :x:

Standard library
  * new theory `ieee_float` formalizing floating-point arithmetic,
    compliant to IEEE-754, mapped to SMT-LIB FP theory.

User features
  * proof strategies: `why3 config` now generates default proof strategies
    using the installed provers. These are available under name "Auto
    level 0", "Auto level 1" and "Auto level 2" in `why3 ide`.
    More details in the manual, section 10.6 "Proof Strategies".
  * counterexamples: better support for array values, support for
    floating-point values, support for Z3 in addition to CVC4.
    More details in the manual, section 6.3.5 "Displaying Counterexamples".

Plugins
  * new input format for a small subset of Python

Provers
  * support for Isabelle 2017 (released Oct 2017)
  * dropped support for Isabelle 2016 (2016-1 still supported) :x:
  * support for Coq 8.6.1 (released Jul 25, 2017)
  * tentative support for Coq 8.7
  * dropped tactic support for Coq 8.4 (proofs still supported) :x:
  * support for CVC4 1.5 (released Jul 10, 2017)
  * support for E 2.0 (released Jul 4, 2017)
  * support for E 1.9.1 (release Aug 31, 2016)

Version 0.87.3, January 12, 2017
--------------------------------

Bug fixes
  * fixed OCaml extraction with respect to ghost parameters
  * assorted bug fixes

Provers
  * support for Alt-Ergo 1.30 (released Nov 21, 2016)
  * support for Coq 8.6 (released Dec 8, 2016)
  * support for Gappa 1.3 (released Jul 20, 2016)
  * dropped support for Isabelle 2015 :x:
  * support for Isabelle 2016-1 (released Dec 2016)
  * support for Z3 4.5.0 (released Nov 8, 2016)

Version 0.87.2, September 1, 2016
---------------------------------

Bug fixes
  * improved well-formedness of extracted OCaml code
  * assorted bug fixes

Version 0.87.1, May 27, 2016
----------------------------

Bug fixes
  * assorted bug fixes

Version 0.87.0, March 15, 2016
------------------------------

Language
  * added two new logical connectives `by` and `so` as keywords :x:

Tools
  * added a command-line option `--extra-expl-prefix` to specify
    additional possible prefixes for VC explanations. Available for
    `why3` commands `prove` and `ide`.
  * removed `jstree` style from the `session` command :x:

Transformations
  * all split transformations respect the `"stop_split"` label now.
    `split_*_wp` is a synonym for `split_*_right` :x:
  * the `split_*_right` transformations split the left-hand side subformulas
    when they carry the `"case_split"` label :x:
  * `split_intro` is now the composition of `split_goal_right` and
    `introduce_premises` :x:

Standard library
  * improved bitvector theories :x:

API
  * renamed functions in module `Split_goal` :x:
  * `split_intro` moved to Introduction :x:

Encoding
  * if a task has no polymorphic object (except for the special
    cases of equality and maps), then the translation to SMT-LIB
    format is direct :x:

Provers
  * dropped support for Alt-Ergo versions older than 0.95.2 :x:
  * support for Alt-Ergo 1.01 (released Feb 16, 2016) and
    non-free versions 1.10 and 1.20
  * support for Coq 8.4pl6 (released Apr 9, 2015)
  * support for Coq 8.5 (released Jan 21, 2016)
  * support for Gappa 1.2.0 (released May 19, 2015)
  * dropped support for Isabelle 2014 :x:
  * support for Isabelle 2015 (released May 25, 2015) and
    Isabelle 2016 (released Feb 17, 2016)
  * support for Z3 4.4.0 (released Apr 29, 2015) and
    4.4.1 (released Oct 5, 2015)
  * support for Zenon 0.8.0 (released Oct 21, 2014)
  * support for Zenon_modulo 0.4.1 (released Jul 2, 2015)

Distribution
  * non-free files have been removed: `boomy` icon set,
    javascript helpers for `why3 session html --style jstree`

Version 0.86.3, February 8, 2016
--------------------------------

Bug fixes
  * assorted bug fixes

Provers
  * fix compilation issues with Coq 8.5
    (the tactic for 8.5 now behaves like `idtac` on successfully proved goals) :x:

Version 0.86.2, October 13, 2015
--------------------------------

Bug fixes
  * assorted bug fixes

Version 0.86.1, May 22, 2015
----------------------------

IDE
  * improved task highlighting for negated premises
    (contributed by Mikhail Mandrykin, AstraVer project)

Provers
  * support for Gappa 1.2 (released May 19, 2015)

Bug fixes
  * `why3doc`: garbled output

Version 0.86, May 11, 2015
--------------------------

Core
  * steps limit for reliable replay of proofs, available for Alt-Ergo
    and CVC4

Transformations
  * new transformations `induction_pr` and `inversion_pr` to reason with
    inductive predicates

Standard library
  * renamed theory `int.NumOfParam` into `int.NumOf`; the predicate `numof`
    now takes some higher-order predicate as argument (no more need
    for cloning). Similar change in modules `array.NumOf`... :x:
  * improved theory `real.PowerReal` :x:
  * new theory: sequences
  * new theories for bitvectors, mapped to BV theories of SMT solvers
    Z3 and CVC4

Provers
  * support for Coq 8.4pl5 (released Nov 7, 2014)
  * support for Z3 4.3.2 (released Oct 25, 2014)
  * support for MetiTarski 2.4 (released Oct 21, 2014)
  * support for Alt-Ergo 0.99.1 (released Dec 30, 2014)
  * support for Alt-Ergo 1.00.prv (released Jan 29, 2015)
  * support for veriT 201410 (released Nov 2014)
  * support for Psyche (experimental,
    http://www.lix.polytechnique.fr/~lengrand/Psyche/)
  * preliminary support for upcoming CVC4 1.5 (steps feature)

IDE
  * config file not automatically saved anymore at exit. Configuration
    is saved on disk for future sessions if, and only if, preferences
    window is exited by hitting the "Save&Close" button
  * right part of main window organized in tabs
  * better explanations and task highlighting
    (contributed by Mikhail Mandrykin, AstraVer project)

Bug fixes
  * bug in interpreter in presence of nested mutable fields
  * IDE: proofs in progress should never be "cleaned"
  * IDE: display warnings after reload

Version 0.85, September 17, 2014
--------------------------------

Langage
  * fix a soundness bug in the detection of aliases when calling a
    WhyML function: some alias could have been forgotten when a type
    variable was substituted with a mutable type :x:

Proof sessions
  * use the full path of identifiers when the user introduces namespaces
    (BTS #17181)

Transformations
  * fix a soundness bug in `compute_in_goal` regarding the handling of
    logical implication. :x:
  * several improvements to `compute_in_goal`:
    - left-hand side of rewrite rules can be any symbols, not only
      non-interpreted ones.
    - perform beta-reduction when possible
    - the maximal number of reduction steps can be increased using meta
      `compute_max_steps`
    - the transformation is documented in details in the manual
  * new transformation `compute_specified`:
    less aggressive variant of `compute_in_goal`.
    Unfolding of definitions is controlled using meta `rewrite_def`
  * fixed a bug in `eliminate_if` when applied on inductive definitions

Provers
  * fixed wrong warning when detecting Isabelle2014

Version 0.84, September 1, 2014
-------------------------------

Tools
  * the file generated by `why3 session html f.mlw` is now
    `f/why3session.html` and not `f/f.html` :x:
  * the default behavior of `why3` has been moved to the `prove` subcommand :x:
  * options `--exec`, `--extract`, and `--realize`, have been moved to
    subcommands: `execute`, `extract`, and `realize` :x:
  * `why3replayer` has been moved to the `replay` subcommand :x:
  * other tools have been moved to `why3` subcommands too: `config`, `doc`, `ide`,
    `session`, `wc`. For local usage, the old commands are still available. :x:

Proof sessions
  * session files are split in two parts: `why3session.xml` and
    `why3shapes`. The latter file contains the checksums and the shapes
    for the goals. That second file is not strictly needed for
    replaying a proof session, it is only useful when input programs
    are modified, to track obsolete goals. If Why3 is compiled with
    compression support (provided by the `ocamlzip` library) then files for
    shapes are compressed into `why3shapes.gz`.

Standard library
  * renamed `array.ArraySorted` into `array.IntArraySorted`;
    `array.ArraySorted` is now generic, with type and order relation parameters :x:
  * reduced amount of `use export` in the standard library: theories
    now only export the symbols they define. Users may need to insert more
    `use import` in their theories (typically `int.Int`, `option.Option`,
    `list.List`, etc.). :x:

Provers
  * fixed Coq printer (former Coq proofs may have to be updated, by removing
    non-emptiness constraints from polymorphic type applications) :x:
  * support for Coq8.4pl4
  * support for Isabelle2014
  * support for CVC4 1.4
  * updated support for TPTP TFA syntax (used by provers Beagle and Princess)

Transformations
  * new transformation `compute_in_goal` that simplifies the goal, by
    computation, as much as possible

Version 0.83, March 14, 2014
----------------------------

Language
  * extra semicolons are now allowed at end of blocks
  * new clause `diverges`; loops and recursive calls not annotated
    with variants will generate a warning, unless the`"diverges`
    clause is given
  * clauses `reads` and `writes` now accept an empty set
  * modified syntax for `abstract`: `abstract <spec> <expr> end` :x:
  * types in quantifiers are now optional
  * formulas and Boolean terms can be used interchangeably

Standard library
  * removed inconsistency in libraries `map.MapPermut` and `array.ArrayPermut`
    (names, definitions, and meaning of symbols `permut...` have been modified) :x:

Provers
  * new version of prover: Coq 8.4pl3
  * new version of prover: Gappa 1.1.0
  * new version of prover: E prover 1.8
  * dropped support for Coq 8.3 :x:
  * improved support for Isabelle2013-2
  * fixed Coq printer (former Coq proofs may have to be updated, with
    extra qualification of imported symbols) :x:

Tools
  * new option `--exec` to interpret WhyML programs; see doc chapter 8
  * new option `--extract` to compile WhyML programs to OCaml;
    see doc chapter 8 and `modules/mach/{int,array}.mlw`
  * `why3replayer` renamed option `-obsolete-only` to `--obsolete-only`,
    `-smoke-detector` to `--smoke-detector`, `-force` to `--force` :x:
  * `why3replayer` now fails replaying if new goals are added :x:

API
  * new type-inferring API for logical terms and program expressions

Miscellaneous
  * fixed compilation bug with lablgtk 2.18

Version 0.82, December 12, 2013
-------------------------------

Core
  * lemma functions
  * polymorphic recursion permitted
  * opaque types

API
  * more examples of use in `examples/use_api/`

Tools
  * `why3session csv` can create graph with option `--gnuplot [png|svg|pdf|qt]`
  * shape algorithm modified (see VSTTE'13 paper) but is
    backward compatible thanks to `shape_version` numbers in
    `why3session.xml` files
  * options name and default of `why3session csv` changed :x:

Miscellaneous
  * emacs: `why.el` renamed to `why3.el` :x:
  * GTK sourceview: `why.lang` renamed to `why3.lang` :x:
  * `Loc.try[1-7]` functions now take location as an optional parameter :x:

Provers
  * new prover: Metitarski (2.2, contribution by Piotr Trojanek)
  * new prover: Metis (2.3)
  * new prover: Beagle (0.4.1)
  * new prover: Princess (2013-05-13)
  * new prover: Yices2 (2.0.4)
  * new prover: Isabelle (2013-2, contribution by Stefan Berghofer)
  * new version of prover: Alt-Ergo 0.95.2
  * new version of prover: CVC4 1.1 & 1.2 & 1.3
  * new version of prover: Coq 8.4pl2
  * new version of prover: Gappa 1.0.0
  * new version of prover: SPASS 3.8ds
  * new version of prover: veriT (201310)

Bug fixes
  * remove extra leading zeros in decimal literals when a prover don't like them
  * PVS output: types are always non-empty
  * PVS: fixed configuration and installation process
  * Coq tactic: now loads dynamic plug-ins
  * bug #15493: correct Coq output for polymorphic algebraic data types
  * wish #15053: Remove proof time from "Goals proved by only one prover" section
    of `why3session info --stats` :x:
  * bug #13736: `why3ml` was slow when there were many inclusions
  * bug #16488: decimals in TPTP syntax
  * bug #16454: do not send arithmetic triggers anymore to alt-Ergo
  * syntax highlighting bugs should be fixed by removing the old language
    file `alt-ergo.lang` from Alt-ergo distribution

Version 0.81, March 25, 2013
----------------------------

Provers
  * experimental support for SPASS >= 3.8 (with types)
  * support for Z3 4.3.*
  * fixed Coq 8.4 support for theory `real.Trigonometry`
  * support for CVC4
  * support for mathematica
  * support for MathSAT5

Core
  * accept type expressions in clone substitutions

WhyML
  * support for relation chains (e.g., `e1 = e2 < e3`)
  * every exception raised in a function must be listed
    in as `raises { ... }` clause. A postcondition may be omitted
    and equals to `true` by default. :x:
  * if a function definition contains a `writes { ... }`
    clause, then every write effect must be listed. If a function
    definition contains a `reads { ... }` clause, then every read
    _and_ write effect must be listed. :x:

Drivers
  * syntax rules, metas, and preludes are inherited
    through cloning. Keyword `cloned` becomes unnecessary and
    is not accepted anymore. :x:


Version 0.80, October 31, 2012
------------------------------

WhyML
  * modified syntax for mlw programs; a summary of changes is
    given in Appendix A of the manual :x:
  * support for type invariants and ghost code

API
  * Ocaml interfaces for constructing program modules

Transformations
  * experimental support for induction on integers and on algebraic types

Interface
  * new system of warnings, that includes:
     - form `exists x, P -> Q`, likely an error
     - unused bound logic variables in `forall`, `exists`, and `let`

Tools
  * replayer: new option `-q`, for running quietly
  * improved output of `why3session latex`; LaTeX macros have
    more arguments :x:
  * modifiers in `--extra-config` are now called `[prover_modifier]`
    instead of just `[prover]` :x:

Provers
  * support for Coq 8.4
  * dropped support for Coq 8.2 :x:
  * support for forthcoming PVS 6.0, including realizations
  * support for iProver and Zenon
  * new output scheme for Coq using type classes, to ensures
    types are inhabited

Drivers
  * theory realizations now use meta `realized_theory` instead
    of `realized` :x:

Version 0.73, July 19, 2012
---------------------------

Core
  * co-inductive predicates

WhyML
  * new construct `abstract e { q }` that matches the structure of the goal

Proof sessions
  * small change in the format. Why3 is still able to
    read session files in the old format.

Standard library
  * fixed a consistency issue with `set.Fset` theory

Tools
  * option `-obsolete-only` for `why3replayer`
  * new option `-e` for `why3session latex` to specify when to
    split tables in parts
  * no more executable `why3ml` (`why3` now handles WhyML files) :x:

Provers
  * support for Z3 4.0
  * workaround for a bug about modulo operator in Alt-Ergo 0.94
  * quotes in identifiers remain quotes in Coq
  * Coq default tactic is now `intros ...` with a pattern

IDE
  * "Clean" was cleaning too much

Miscellaneous
  * completed support for the "Out Of Memory" prover result

Version 0.72, May 11, 2012
--------------------------

Provers
  * Coq: new tactic `why3` to call external provers as oracles
  * Coq: new feature: theory realizations (see manual, chapter 9)

Tools
  * new tool `why3session` (see manual, section 6.7)
  * new tool `why3doc` (see manual, section 6.8)
  * support for multiple versions of the same prover (see manual, section 5.5)

IDE
  * new features, including prover upgrade, alternate editors

Miscellaneous
  * complete support for limiting provers' memory usage
  * improved support on Microsoft Windows
  * new parser for TPTP files with support for the newest
    TFA1 format (TPTP with polymorphic types and arithmetic)

Bug fixes
  * fixed BTS 14221
  * fixed BTS 14190
  * fixed BTS 12457
  * fixed BTS 13854
  * fixed BTS 13849

Language
  * new syntax `constant x:ty` and `constant x:ty = e` to
    introduce constants, as an alternative to `function`

API
  * `Dtype` declaration kind is split into two: `Dtype` for
    declarations of a single abstract type or type alias, and
    `Ddata` for a list of (mutually recursive) algebraic types.
    Similarly, `Dlogic` declaration kind is split into `Dparam` for
    a single abstract function/predicate symbol and `Dlogic` for
    a list of (mutually recursive) defined symbols.

Version 0.71, October 13, 2011
------------------------------

Examples
  * a lot of new program examples in directory examples/programs

Tools
  * `why3replayer`: new option `-latex` to output a proof session in LaTeX format

WhyML
  * significant improvement of the efficiency of the WP calculus
  * fixed labels and source locations in WPs

IDE
  * better coloring and source positioning including from front-ends
    such as Krakatoa and Jessie plugin of Frama-C

Proof sessions
  * during reload, new method for pairing old and new subgoals
    based on goal shapes, stored in database.
  * prover versions are stored in database. A proof is
    marked obsolete if it was made by a prover with another version
    than the current.

Version 0.70, July 6, 2011
--------------------------

WhyML
  * language and VC generator

Language
  * record types
    - introduced with syntax `type t = {| a:int; b:bool |}`
      actually syntactic sugar for `type t = 'mk t' (a:int) (b:bool)`
      i.e. an algebraic with one constructor and projection functions
    - a record expression is written `{| a = 1; b = True |}`
    - access to field `a` with syntax `x.a`
    - update with syntax `{| x with b = False |}`
    - record patterns
  * new syntax for conjunction `/\` and disjunction `\/`
    (`and` and `or` do not exist anymore) :x:
  * `logic` is not a keyword anymore, use `function` and `predicate` :x:

Tools
  * new tool `why3replayer`: batch replay of a Why3 session created in IDE

Provers
  * Alt-Ergo, Z3, CVC3, Yices: support for built-in theory of arrays

IDE
  * interactive detection of provers disabled because incompatible
    with session. Detection must be done with `why3config --detect-provers`
  * tool "Replay" works
  * tool "Reload" reloads the file from disk. No need to exit IDE anymore
  * does not use `Threads` anymore, thanks to `Call_provers.query_call`
  * displays explanations using labels of the form `"expl:..."`
  * dropped dependency on `Sqlite3`

API
  * functions to create an environment are now exported from `Env` :x:
  * calls to prover can now be asynchronous.
    `Driver.prove_task` now returns some intermediate value
    (of type `prover_call`), which can be queried in two ways:
    - blocking way with `Call_provers.wait_on_call`
    - non-blocking way with `Call_provers.query_call`

    So old code performing `prove_task t () ()` should be translated to
    `wait_on_call (prove_task t ()) ()`. :x:

Bug fixes
  * IDE: bug 12244 resolved by using `Task.task_equal`
  * Alt-Ergo: no triggers for `exists` quantifier
  * Coq: polymorphic inductive predicates
  * Coq: fixed bug 12934: type def with several type params

Version 0.64, February 16, 2011
-------------------------------

Language
  * `/\` renamed into `&&` and `\/` into `||` :x:
  * algebraic types: must be well-founded, non-positive constructors
    are forbidden, recursive functions and predicates must
    structurally terminate
  * accept lowercase names for axioms, lemmas, goals, and cases in
    inductive predicates

Transformations
  * `split-goal` does not split under disjunction anymore

Tools
  * `why.conf` is no more looked for in the current directory; use `-C` or
    `WHY3CONFIG` instead
  * when `why.conf` is changed, a backup copy is made in `why.conf.bak`
  * `why.conf` now contains a magic number; configuration must be
    rebuilt with `why3config` if the magic number has changed
  * `why3config`: `--autodetect-provers` renamed to `--detect-provers`,
                  `--autodetect-plugins` renamed to `--detect-plugins`;
    new option `--detect` to perform both detections
  * `why3config`: `--conf_file` is replaced by `-C` and `--config`

Drivers
  * TPTP: encoding by explicit polymorphism is not anymore the
    default encoding for TPTP provers. It is now forbidden to use this
    encoding in presence of finite types.

IDE
  * source file names are stored in database with paths relative
    to the database, so that databases are now easier to move from a
    machine to another (e.g when they are stored in source control
    repositories)

Provers
  * better Gappa output: support for `sqrt`, for negative constants

Miscellaneous
  * `configure`: fixed `--enable-local`
  * `configure`: if possible, use `ocamlfind` to find `lablgtk2` and `sqlite3`
  * labels in terms and formulas are not printed by default

Version 0.63, December 21, 2010
-------------------------------

  * first public release. See release notes in manual

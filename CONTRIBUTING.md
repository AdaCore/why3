Welcome, contributor, to the Why3 verification platform!

If you wish to contribute, open an issue or otherwise interact with our [Gitlab](https://gitlab.inria.fr/why3/why3), you will need to have an Inria account.
External users can file bug reports using our [mailing list](mailto:why3-club@groupes.renater.fr). We are sorry for the inconvenience.

# Building

To build Why3 locally you will need a functional installation of OCaml (at
least 4.09), `menhir`, `zarith`, and `autoconf`. You can set up your developer
build using the following commands:

```
autoconf
./configure --enable-local # stores the built binaries under ./bin
make
```

## Building Documentation

Building the Why3 documentation requires an installation of Sphinx, as well as the `sphinxcontrib-bibtex` package. If your package manager does not have up to date versions of these packages, or they otherwise fail to install, you can install them using `pip3` as follows:

```
pip3 install sphinx sphinxcontrib-bibtex
```

You will need to re-configure Why3 to enable documentation building. Once it has been configured, documentation can be built by running `make doc`.

# Testing

To execute the Why3 tests run:

```
./bench/bench
```

## Running specific tests

You may run specific classes of tests by specifying them on the command line.
The full listing of classes can be obtained from `-help`.

For example to run the 'good file' and 'bad file' tests, use:

```
./bench/bench goodfiles badfiles
```

## Gitlab CI

Every new commit pushed on the gitlab repository invokes an continuous
integration check. The description on how to upgrade this CI procedure
is specifically done in `misc/ci.md`

## Adding new test suites

To add a new directory of tests add a new line in `bench/bench`. The suite should be added to the relevant block, which is determined by the kind of assertion it performs. For example, if you wished to add a set of files which should successfully prove, add a line like `goods path/to/tests` to the appropriate block.

Certain tests, those in `examples/`, `examples/bts`, `examples/programs` and `examples/check-builtin` are replayed every night on Moloch. To ensure accuracy and avoid flakiness, the sessions for these tests must be created on Moloch as well.

## Nightly CI

Every night, the latest master is tested against a series of standard
configurations, on Moloch (`moloch.lri.fr`). This ensures that
regressions are caught across a wide array of different prover
versions and families. The results of Nightly CI are emailed to a set
of selected developers emails each morning.

If you require access to Moloch in order to update sessions or test a new prover, ask one of the maintainers for help.

# Standards

Why3 uses a Pull Request development model. Contributions should be made to separate branches and a Merge Request should be opened in Gitlab, explaining the contents and purpose of its contents.

While code review is not strictly enforced it is *highly* encouraged.

## Commits

Every commit should:

- Compile, and pass CI.
- Be stripped of trailing whitespace.
- Use appropriate indentation.
- Be limited to 80 columns.
- Have a clear and relevant commit message
- Be as functionally isolated as possible

# Contributing to counterexamples generation and checking

The module `src/core/model_parser` contains the main data structure
for counterexamples.

Parser functions for counterexamples must be declared in driver files
(e.g. declaring `model_parser "smtv2"` somewhere).  Such functions
should first be registered using `Model_parser.register_model_parser`.
The latter function takes as input a so-called `raw_model_parser`
(e.g. `Smtv2_model_parser.parse`).  This `raw_model_parser` is an
input of the internal function `Model_parser.model_parser`, which is
the main function for counterexamples generation.  A
`raw_model_parser` is a function that processes a solver textual
output and produces a preliminary structure for counterexamples, which
is completed by `Model_parser.model_parser`.

So, as mentioned above, an example of a `raw_model_parser`, for SMTv2
solvers, is `Smtv2_model_parser.parse`, which makes use of another
data type `Smtv2_model_defs.function_def`.  This specific
`Smtv2_model_parser.parse` function proceeds in 2 main phases:

- first transforms the textual output into an S-expression,
- then the latter S-expression is transformed into a
  `Model_parser.model_element list`.

The `raw_model_parser` functions are using the variable names as
printed by the printer.  It is only the `Model_parser.build_model_rec`
function that recovers the original Why3 name from the
`printing_info`.  The type `printing_info` is declared in module
`src/core/printer`.  Task printers are taking as arguments a record of
type `Printer.printer_args`.  The field `printing_info` is supposed to
be modified in place by printers.

# Profiling

Profiling execution of Why3 can be performed out-of-the-box using
under Linux using `perf`. A typical usage is

```
perf record --call-graph=dwarf -- why3 command <options> <arguments>
perf report
```

Note that `perf` may complain you don't have enough privileges. To change
your configuration for the current session only, execute

```
sysctl kernel.perf_event_paranoid=2
```

or, to make this setting permanent, add the line

```
kernel.perf_event_paranoid = 2
```

to `/etc/sysctl.conf`.

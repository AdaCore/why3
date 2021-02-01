Welcome, contributor, to the Why3 verification platform!

If you wish to contribute, open an issue or otherwise interact with our [Gitlab](https://gitlab.inria.fr/why3/why3), you will need to have an INRIA account.
External users can file bug reports using our [mailing list](mailto:why3-club@lists.gforge.inria.fr). We're sorry for the inconvenience.

# Building

To build Why3 locally you will need a functional installation of OCaml (at least 4.05), `menhir`, `num` and `autoconf`. You can set up your developer build using the following commands

```
autoconf
./configure --enable-local # stores the built binaries under ./bin
make
```

Note: there can be issues around Num, recall and document those.


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

You may run specific classes of tests through the `-only` flag, the full listing of classes can be obtained from `-help`.

For example to run the 'good file' tests, use:

```
./bench/bench -only goodfiles
```

## Adding new test suites

To add a new directory of tests add a new line in `bench/bench`. The suite should be added to the relevant block, which is determined by the kind of assertion it performs. For example, if you wished to add a set of files which should successfully prove, add a line like `goods path/to/tests` to the appropriate block.

Certain tests, those in `examples/`, `examples/bts`, `examples/programs` and `examples/check-builtin` are replayed every night on Moloch. To ensure accuracy and avoid flakiness, the sessions for these tests must be created on Moloch as well.

## Nightly CI

Every night, the latest master is tested against a series of standard configurations, on Moloch (`moloch.lri.fr`). This ensures that regressions are caught across a wide array of different prover versions and families. The results of Nightly CI are emailed in the `why3-commits@lists.gforge.inria.fr` mailing list each morning.

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

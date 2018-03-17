# Archsat

Archsat is a prototype SMT solver combining traditional SMT solving
techniques for ground resoning, tableaux method and rewriting for
quantified formulas, and superposition for unification modulo equalities and
modulo rewriting.

## LICENSE

TODO

## Installation

### Dependencies

Dependencies of archsat are listed in the opam file at the root of the repo.
Most are relatively standard and easily instalable via opam (though you should
not need to install them manually is you install archsat via opam), however,
some of the work done for archsat was splitted into standalone packages,
which are currently still under developpement and need to be pinned (since
bugfixes happen from time to time). More specifically, the `dolmen` package used
for parsing many different input languages, and the `msat` package providing
a functorized sat/smt/mcsat solver should be pinned to their dev repo using the
following command:

```
opam pin add --dev-repo msat
opam pin add --dev-repo dolmen
```

### Using opam

The easiest way to install archsat is to pin the repo and let opam
install the package (after having pinned the dev repos for `msat` and
`dolmen`):

```
opam pin add archsat /path/to/git/repo
```

Once installed via opam, an `archsat` binary should be available the path,
as well as manpages for archsat.

### Manually

One can install archsat manually, though it requires dependencies to be explicitly
installed. The list of dependencies can be found in the `opam` file at the root of
the repository. One can then run:

```
MANDIR=/some/path BINDIR=/some/other/path make install
```

Specifying the `MANDIR` and `BINDIR` is necessary to specify where to install
the binary and the manpages.

### Tests

The archsat repo includes some tests for the binary, in the `tests` directory,
these can be run using the command:

```
make test
```

For unit tests of internal functions, see `src/README.md`.

## Usage

The common and profiling options of the archsat binary should be fairly well documented
in the manpage (as well as when using the `--help` command). Advanced options may require
some more knowledge of the prover's internals to be used correctly.

In case of unhelpful or unsufficiently clear explanations, don't hesitate
to submit a bug report.


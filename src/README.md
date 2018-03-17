# Archsat SRC

## Build

Once dependencies are installed the following can be used:

- `make bin` build the `main.native` binary
- `make lib` builds the archsat library (mainly used for unit testing currently)
- `make test` builds the unit test binary and launches it (it cna take a few minutes to run)
- `make clean` cleans build artifacts

## Code organisation

The code is divided into the following files and folders:

- `main.ml`: main file used for the binary
- `base/*.ml`: definitions for the basic datatypes used in the prover,
  most notably `base/expr.ml` defines the first-order expressions manipulated
  throughout the prover
- `core/*.ml`: implements the core functions implementing proof search
- `algos/*.ml`: contains implementations of algorithms used for proof search,
  these algorithms are tied to the structure defined in `base/expr.ml`, but not
  to the proof search algorithm defined in `core/`
- `debug/` defines special implementations for debugging/logging and profiling used
  bu the archsat binary
- `input/*.ml` defines various input functions for the binary
- `middle/*.ml` defines some helper functions for the binary (such as timeout/memory
  limit implementations, pipelines, etc...)
- `util/` and `misc/` : various utilities, could maybe be merged one day
- `output/*.ml` defines functions for outputting answers in different specifications,
  such as archsat own answers, and the SZS antology
- `proof/*.ml` deinfes functions for printing proof in various languages, such as
  graphs using graphviz/dot, Coq formal proofs and soon dedukti
- `test/` containes unit-testing specifications for the library functions



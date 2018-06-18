
BIN=../archsat
OPT=--infer
NAME=solve/logic
TESTS= $(patsubst %,%.unsat,$(shell find . -name '*.smt2' -o -name '*.p' | sort -n))

include ../Makefile.shared


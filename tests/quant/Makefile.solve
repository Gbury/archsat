
BIN=../archsat
OPT=-x +meta --meta.find=auto
NAME=solve/quantifiers
TESTS= $(patsubst %,%.unsat,$(shell find . -name '*.smt2' -o -name '*.p' | sort -n))

include ../Makefile.shared


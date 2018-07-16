#!/usr/bin/env bash

perf record --call-graph=dwarf $@

perf script \
  | stackcollapse-perf.pl --kernel \
  | sed 's/caml//g' \
  | flamegraph.pl > perf.svg


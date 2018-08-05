#!/usr/bin/env bash

perf record --call-graph=dwarf $@

perf report


#!/bin/bash
# uses hyperfine: https://github.com/sharkdp/hyperfine
cabal build

hyperfine --warmup 2 --export-markdown benchmark.md \
    'cabal run effectful-cp -- "naive"' \
    'cabal run effectful-cp -- "handlers_it"' \
    'cabal run effectful-cp -- "handlers_dbs20"' \
    'cabal run effectful-cp -- "experiment_it"' \
    'cabal run effectful-cp -- "experiment_dbs20"' \
    'cabal run effectful-cp -- "NbsDbsComp"' \
    'cabal run effectful-cp -- "NbsDbsOnly"' 
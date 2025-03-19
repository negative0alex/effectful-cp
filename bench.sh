#!/bin/bash
# uses hyperfine: https://github.com/sharkdp/hyperfine
cabal build

hyperfine --warmup 2 --export-markdown benchmark.md \
    'cabal run effectful-cp -- "handlers_dbs20"' \
    'cabal run effectful-cp -- "nbs_dbs_comp"' \
    'cabal run effectful-cp -- "nbs_dbs_only"' \
    'cabal run effectful-cp -- "traverse_dbs20"' \
    'cabal run effectful-cp -- "traverse_nbs_dbs"' \
    'cabal run effectful-cp -- "all_dbs20"' \
    # 'cabal run effectful-cp -- "naive"' \
    # 'cabal run effectful-cp -- "handlers_it"' \
    # 'cabal run effectful-cp -- "experiment_it"' \
    # 'cabal run effectful-cp -- "experiment_dbs20"' \
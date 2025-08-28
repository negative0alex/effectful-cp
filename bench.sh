#!/bin/bash
# uses hyperfine: https://github.com/sharkdp/hyperfine
cabal build

hyperfine --export-markdown benchmark.md \
    'cabal run effectful-cp -- "bb_lds_rand"' \
    'cabal run effectful-cp -- "bb_lds_rand_old"' \
    'cabal run effectful-cp -- "bb_lds_rand_staged"' \
    'cabal run effectful-cp -- "bb_lds_rand_staged_old"' \
    'cabal run effectful-cp -- "bb_lds_rand_opt"' 
     
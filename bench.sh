#!/bin/bash
# uses hyperfine: https://github.com/sharkdp/hyperfine
cabal build

hyperfine --export-markdown benchmark.md \
    'cabal run effectful-cp -- "bb_h"' \
    'cabal run effectful-cp -- "bb_s"' \
    # 'cabal run effectful-cp -- "handlers_it"' \
    # 'cabal run effectful-cp -- "handlers_it2"' \
    # 'cabal run effectful-cp -- "example_1"' \
    # 'cabal run effectful-cp -- "example_2"' \
    # 'cabal run effectful-cp -- "example_3"' \
    # 'cabal run effectful-cp -- "example_o"' \
    # 'cabal run effectful-cp -- "example_s"' \
    # 'cabal run effectful-cp -- "example_h"' \
    # 'cabal run effectful-cp -- "staged_lds_nbs_dbs_opt"' \
    # 'cabal run effectful-cp -- "staged_lds_nbs_dbs"' \
    # 'cabal run effectful-cp -- "handlers_lds_nbs_dbs"' \
    # 'cabal run effectful-cp -- "staged_nbs_dbs_opt"' \
    # 'cabal run effectful-cp -- "staged_rand_dbs"' \
    # 'cabal run effectful-cp -- "handlers_rand_dbs"' \
    # 'cabal run effectful-cp -- "staged_dbs"' \
    # 'cabal run effectful-cp -- "staged_nbs_dbs"' \
    # 'cabal run effectful-cp -- "traverse_dbs"' \
    # 'cabal run effectful-cp -- "traverse_nbs_dbs"' \
    # 'cabal run effectful-cp -- "handlers_dbs"' \
    # 'cabal run effectful-cp -- "handlers_nbs_dbs"' \
    # 'cabal run effectful-cp -- "not_really"' \
    # 'cabal run effectful-cp -- "slightly"' \
    # 'cabal run effectful-cp -- "nbs_dbs_comp"' \
    # 'cabal run effectful-cp -- "nbs_dbs_only"' \
    # 'cabal run effectful-cp -- "all_dbs"' \
    # 'cabal run effectful-cp -- "naive"' \
    # 'cabal run effectful-cp -- "experiment_it"' \
    # 'cabal run effectful-cp -- "experiment_dbs"' \

    # printCode :: Code Q a -> IO ()
    # printCode code = do x <- runQ (unTypeCode code); putStrLn $ pprint x
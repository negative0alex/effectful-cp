#!/bin/bash
# uses hyperfine: https://github.com/sharkdp/hyperfine
cabal build

hyperfine --export-markdown benchmark.md \
    'cabal run effectful-cp -- "staged_lds_nbs_dbs_opt"' \
    'cabal run effectful-cp -- "staged_lds_nbs_dbs"' \
    'cabal run effectful-cp -- "handlers_lds_nbs_dbs"' \
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
    # 'cabal run effectful-cp -- "handlers_it"' \
    # 'cabal run effectful-cp -- "experiment_it"' \
    # 'cabal run effectful-cp -- "experiment_dbs"' \

    # printCode :: Code Q a -> IO ()
    # printCode code = do x <- runQ (unTypeCode code); putStrLn $ pprint x
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import Staging.Toplevel as Staging
import System.Environment (getArgs)
import BranchAndBound (gmodel)
import BranchAndBound (bb)
import Transformers
import BranchAndBound (newBound)
import Eval


bbLdsRand = it . (bb newBound) . (lds 5000) . (rand 123)

main :: IO ()
main = do
  arg <- head <$> getArgs
  let graph = gmodel 50
      sols = case arg of
        "bb_lds_rand_staged" -> dfsS bbLdsRandStaged graph
        "bb_lds_rand" -> dfs bbLdsRand graph
        _ -> []
  print $ sols

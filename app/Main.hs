{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
module Main where
import qualified Handlers
import qualified Queens
import qualified HandlersExperiment
import System.Environment (getArgs)
import qualified CombinedHandlers
import Staging


main :: IO ()
main = do
  arg <- head <$> getArgs
  let queens = 10
      depth = 25
      nodes = 500000
      disc = 5000000
      seed = 2801
      sols = case arg of 
        "naive" -> Handlers.testNaive $ Queens.nqueens queens
        "handlers_it" -> Handlers.testIt $ Queens.nqueens queens
        "handlers_dbs" -> Handlers.testDbs depth $ Queens.nqueens queens
        "handlers_nbs_dbs" -> Handlers.testNbsDbs nodes depth $ Queens.nqueens queens
        "handlers_lds_nbs_dbs" -> Handlers.testLdsNbsDbs disc nodes depth $ Queens.nqueens queens
        "handlers_rand_dbs" -> Handlers.testRandDbs seed depth $ Queens.nqueens queens
        "experiment_it" -> HandlersExperiment.testSolver $ HandlersExperiment.nqueens queens 
        "experiment_dbs" -> HandlersExperiment.testSolverDbs depth $ HandlersExperiment.nqueens queens
        "nbs_dbs_comp" -> Handlers.testNbsDbs nodes depth $ Queens.nqueens queens
        "nbs_dbs_only" -> CombinedHandlers.testNbsAfterDbs nodes depth $ Queens.nqueens queens
        "traverse_dbs" -> CombinedHandlers.testDbsTraverse depth $ Queens.nqueens queens
        "traverse_nbs_dbs" -> CombinedHandlers.testNbsAfterDbsTraverse nodes depth $ Queens.nqueens queens
        "all_dbs" -> HandlersExperiment.testAllDbs depth $ HandlersExperiment.nqueens queens
        "not_really" -> CombinedHandlers.testDbsNotReallyCPS depth $ Queens.nqueens queens
        "slightly" -> CombinedHandlers.testDbsSlightlyCPS depth $ Queens.nqueens queens
        "staged_dbs" -> if depth == 25 then Staging.testStagedDbs $ Queens.nqueens queens else []
        "staged_nbs_dbs" -> if depth == 25 && nodes == 500000 then 
            Staging.testStagedDbsNbs $ Queens.nqueens queens else []  
        "staged_lds_nbs_dbs" -> if depth == 25 && nodes == 500000 && disc == 5000000 then 
            Staging.testStagedDbsNbsLds $ Queens.nqueens queens else []
        "staged_rand_dbs" -> if depth == 25 && seed == 2801 then 
            Staging.testStagedDbsRand $ Queens.nqueens queens else []
        _ -> []
  print sols
  

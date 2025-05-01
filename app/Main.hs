{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
module Main where
import qualified Handlers
import qualified Queens
import qualified Experiments.HandlersExperiment
import System.Environment (getArgs)
import qualified Experiments.CombinedHandlers
import Staging.Staging as Staging


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
        "experiment_it" -> Experiments.HandlersExperiment.testSolver $ Experiments.HandlersExperiment.nqueens queens 
        "experiment_dbs" -> Experiments.HandlersExperiment.testSolverDbs depth $ Experiments.HandlersExperiment.nqueens queens
        "nbs_dbs_comp" -> Handlers.testNbsDbs nodes depth $ Queens.nqueens queens
        "nbs_dbs_only" -> Experiments.CombinedHandlers.testNbsAfterDbs nodes depth $ Queens.nqueens queens
        "traverse_dbs" -> Experiments.CombinedHandlers.testDbsTraverse depth $ Queens.nqueens queens
        "traverse_nbs_dbs" -> Experiments.CombinedHandlers.testNbsAfterDbsTraverse nodes depth $ Queens.nqueens queens
        "all_dbs" -> Experiments.HandlersExperiment.testAllDbs depth $ Experiments.HandlersExperiment.nqueens queens
        "not_really" -> Experiments.CombinedHandlers.testDbsNotReallyCPS depth $ Queens.nqueens queens
        "slightly" -> Experiments.CombinedHandlers.testDbsSlightlyCPS depth $ Queens.nqueens queens
        "staged_dbs" -> if depth == 25 then Staging.testStagedDbs $ Queens.nqueens queens else []
        "staged_nbs_dbs" -> if depth == 25 && nodes == 500000 then 
            Staging.testStagedDbsNbs $ Queens.nqueens queens else []  
        "staged_lds_nbs_dbs" -> if depth == 25 && nodes == 500000 && disc == 5000000 then 
            Staging.testStagedDbsNbsLds $ Queens.nqueens queens else []
        "staged_rand_dbs" -> if depth == 25 && seed == 2801 then 
            Staging.testStagedDbsRand $ Queens.nqueens queens else []
        "staged_nbs_dbs_opt" -> if depth == 25 && nodes == 500000 then 
            Staging.testStagedDbsNbsOpt $ Queens.nqueens queens else []
        "staged_lds_nbs_dbs_opt" -> if depth == 25 && nodes == 500000 && disc == 5000000 then 
            Staging.testStagedDbsNbsLdsOpt $ Queens.nqueens queens else []
        _ -> []
  print $ length sols
  

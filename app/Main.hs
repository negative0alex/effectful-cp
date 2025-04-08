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
import Language.Haskell.TH
import Effects (runEffects, (:+:))
import Solver (run)
import Handlers (eval)
import StagedHandlers (dbsTrans)
import Solver (Solver)
import CPSolve (CPSolve)
import NonDet (NonDet)
import Effects (Void)
import Control.Monad.Free
import StagedHandlers
import Staging


main :: IO ()
main = do
  arg <- head <$> getArgs
  let queens = 10
  let depth = 25
  let nodes = 500000
  let sols = case arg of 
        "naive" -> Handlers.testNaive $ Queens.nqueens queens
        "handlers_it" -> Handlers.testIt $ Queens.nqueens queens
        "handlers_dbs20" -> Handlers.testDbs depth $ Queens.nqueens queens
        "experiment_it" -> HandlersExperiment.testSolver $ HandlersExperiment.nqueens queens 
        "experiment_dbs20" -> HandlersExperiment.testSolverDbs depth $ HandlersExperiment.nqueens queens
        "nbs_dbs_comp" -> Handlers.testNbsDbs nodes depth $ Queens.nqueens queens
        "nbs_dbs_only" -> CombinedHandlers.testNbsAfterDbs nodes depth $ Queens.nqueens queens
        "traverse_dbs20" -> CombinedHandlers.testDbsTraverse depth $ Queens.nqueens queens
        "traverse_nbs_dbs" -> CombinedHandlers.testNbsAfterDbsTraverse nodes depth $ Queens.nqueens queens
        "all_dbs20" -> HandlersExperiment.testAllDbs depth $ HandlersExperiment.nqueens queens
        "not_really20" -> CombinedHandlers.testDbsNotReallyCPS depth $ Queens.nqueens queens
        "slightly20" -> CombinedHandlers.testDbsSlightlyCPS depth $ Queens.nqueens queens
        _ -> []
  print sols
  

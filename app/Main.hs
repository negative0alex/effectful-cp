module Main where
import qualified Handlers
import qualified Queens
import qualified HandlersExperiment
import System.Environment (getArgs)

main :: IO ()
main = do
  arg <- head <$> getArgs
  let sols = case arg of 
        "handlers_it" -> Handlers.testIt $ Queens.nqueens 10
        "handlers_dbs20" -> Handlers.testDbs 20 $ Queens.nqueens 10
        "experiment_it" -> HandlersExperiment.testSolver $ HandlersExperiment.nqueens 10 
        "experiment_dbs20" -> HandlersExperiment.testSolverDbs 20 $ HandlersExperiment.nqueens 10
        _ -> []
  print sols
  

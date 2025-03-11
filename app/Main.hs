module Main where
import qualified Handlers
import qualified Queens

main :: IO ()
main = do
  let sols = Handlers.testDbs 20 $ Queens.nqueens 10
  print sols
  

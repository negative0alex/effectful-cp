{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import qualified BranchAndBound
import qualified Experiments.CombinedHandlers
import qualified Handlers
import qualified Queens
import qualified Queens2
import Staging.Staging as Staging
import System.Environment (getArgs)

main :: IO ()
main = do
  arg <- head <$> getArgs
  let sols = case arg of
        _ -> []
  print $ sols

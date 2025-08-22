{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -ddump-splices #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Staging.Toplevel where
import Prelude hiding (fail)
import Staging.Direct
import Eval (SearchTree)
import FD.OvertonFD (OvertonFD)
import Control.Monad.Free (Free)
import Effects.Solver (SolverE, runSolver)
import Solver (Solver, run)

dfsS :: (Solver solver) => (SearchTree solver a -> Free (SolverE solver) [a]) -> SearchTree solver a -> [a]
dfsS search model = run . runSolver . search $ model

bbLdsRandStaged :: SearchTree OvertonFD a -> Free (SolverE OvertonFD) [a] 
-- seed discrepancy
bbLdsRandStaged = $$(bbLdsRandCode 123 5000) []

justBBStaged :: SearchTree OvertonFD a -> Free (SolverE OvertonFD) [a]  
justBBStaged = $$justBBCode []


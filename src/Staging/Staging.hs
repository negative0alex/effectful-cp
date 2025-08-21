{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -ddump-splices #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Staging.Staging where
import Effects.CPSolve
import Control.Monad.Free
import Effects.Core
import Handlers
import Effects.NonDet
import Solver
import Prelude hiding (fail)
import Staging.Handlers
import Staging.Optimisation
import Language.Haskell.TH
import qualified Staging.Handlers as Staging
import Queens (nqueens)
import Staging.Effectful (bnbStaged, bbBench)
import FD.OvertonFD
import Effects.Solver
import BranchAndBound (gmodel)

testStaged :: Solver solver => 
  (Free (NonDet :+: Void) a -> Free Void [a]) -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testStaged st model = run $ runEffects . st <$> eval model

-- ---------------------------------------------------------------------------------------

stagedDfsDbs25 :: Free (NonDet :+: Void) a -> Free Void [a]
stagedDfsDbs25 = $$(stagedDbs25) []

testStagedDbs :: (Solver solver) => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testStagedDbs = testStaged stagedDfsDbs25

-- ---------------------------------

stagedDfsDbsNbs :: Free (NonDet :+: Void) a -> Free Void [a]
stagedDfsDbsNbs = $$(stagedDbsNbs) []

testStagedDbsNbs :: (Solver solver) => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testStagedDbsNbs = testStaged stagedDfsDbsNbs

-- ---------------------------------

stagedDfsDbsNbsLds :: Free (NonDet :+: Void) a -> Free Void [a]
stagedDfsDbsNbsLds = $$(stagedDbsNbsLds) []

testStagedDbsNbsLds :: (Solver solver) => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testStagedDbsNbsLds = testStaged stagedDfsDbsNbsLds

-- ---------------------------------

stagedDfsRand2801 :: forall a. Free (NonDet :+: Void) a -> Free Void [a]
stagedDfsRand2801 = $$(stage1 @[( (), Free (NonDet :+: Void) a )] randTrans2801) []

testStagedRand2801 :: Solver solver => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testStagedRand2801 = testStaged stagedDfsRand2801 

-- ---------------------------------

stagedDfsDbsRand :: forall a. Free (NonDet :+: Void) a -> Free Void [a]
stagedDfsDbsRand = $$(stage1 @[( (Int, ()), Free (NonDet :+: Void) a )] dbsRandTrans) []

testStagedDbsRand :: Solver solver => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testStagedDbsRand = testStaged stagedDfsDbsRand

-- ---------------------------------

stagedDfsDbsNbsOpt :: Free (NonDet :+: Void) a -> Free Void [a]
stagedDfsDbsNbsOpt = $$(dbsNbs') []

testStagedDbsNbsOpt :: Solver solver => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testStagedDbsNbsOpt = testStaged stagedDfsDbsNbsOpt

-- ---------------------------------

stagedDfsDbsNbsLdsOpt :: Free (NonDet :+: Void) a -> Free Void [a]
stagedDfsDbsNbsLdsOpt = $$(dbsNbsLds') []

testStagedDbsNbsLdsOpt :: Solver solver => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testStagedDbsNbsLdsOpt = testStaged stagedDfsDbsNbsLdsOpt

-- ---------------------------------

example :: Free (NonDet :+: Void) a -> Free Void [a]
example = $$(stagedBigExample) []

testExample :: Solver solver => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testExample = testStaged example

example' :: Free (NonDet :+: Void) a -> Free Void [a]
example' = $$(Staging.Optimisation.exampleBig') []

testExample' :: Solver solver => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testExample' = testStaged Staging.Staging.example'

veryBigStaged :: [[Int]]
veryBigStaged = testStaged ($$(Staging.stagedVeryBigExample) []) (nqueens 12)

veryBigOptimised :: [[Int]]
veryBigOptimised = testStaged ($$(Staging.Optimisation.exampleVeryBig') []) (nqueens 12)

----

square :: Num a => a -> a
square x = x * x 

five :: Int 
five = $$two_plus_three

powern :: Integer -> Code Q Integer -> Code Q Integer 
powern pow x
  | pow == 0 = [|| 1 ||]
  | pow == 1 = x
  | pow `mod` 2 == 0 = [|| square $$(powern (pow `div` 2) x) ||]
  | otherwise = [|| $$x * $$(powern (pow - 1) x) ||]

power :: Integer -> CodeQ (Integer -> Integer)
power = \pow -> codeCurry $ powern pow

--

bb :: Free (CPSolve OvertonFD :+: NonDet :+: SolverE OvertonFD) a -> Free (SolverE OvertonFD) [a]
bb = $$bnbStaged []

testBb :: Int -> [Int]
testBb n = run . runSolver $ bb (gmodel n)

bbBenchStaged :: Free (CPSolve OvertonFD :+: NonDet :+: SolverE OvertonFD) a -> Free (SolverE OvertonFD) [a]
bbBenchStaged = $$(bbBench 2501 50) []

testBbBench :: Int -> [Int]
testBbBench n = run . runSolver $ bbBenchStaged (gmodel n)


{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module BranchAndBound where

import Control.Monad.Free (Free (..))
import Effects.CPSolve (CPSolve, dynamic, exists, (@<), (@>))
import Effects.Core ((:+:) (..))
import Effects.NonDet (NonDet (..))
import Effects.Solver (SolverE, runSolver, solve)
import Eval
import FD.OvertonFD (OvertonFD, fd_domain, fd_objective)
import Queens
import Solver (Solver (..))
import Transformers (Transformer, it, lds, makeTEff, rand)
import Prelude hiding (fail)

type Bound solver a =
  Free (CPSolve solver :+: NonDet :+: SolverE solver) a ->
  Free (CPSolve solver :+: NonDet :+: SolverE solver) a

type NewBound solver a = solver (Bound solver a)

data BBEvalState solver a = BBP Int (Bound solver a)

bb :: (Solver solver) => NewBound solver a -> Transformer Int (BBEvalState solver a) solver a
bb newBound = makeTEff
  0
  (BBP 0 id)
  (\(BBP v _) -> solve newBound >>= \bound' -> pure (BBP (v + 1) bound'))
  pure
  pure
  $ \v es@(BBP nv bound) tree -> if nv > v then (nv, es, bound tree) else (v, es, tree)

bbSolve :: CSP' a -> [a]
bbSolve model = run . runSolver . it . (bb newBound) . (eval []) $ model

newBound :: forall a. NewBound OvertonFD a
newBound = do
  obj <- fd_objective
  dom <- fd_domain $ obj
  let val = head dom
  return ((\tree -> obj @< val /\ tree) :: Bound OvertonFD a)

bbBench :: Int -> [Int]
bbBench n = run . runSolver . it . (bb newBound) . (lds 500) . (rand 2501) . (eval []) $ (gmodel n)

----------------------------------------------------------

gmodel :: Int -> CSP' Int
gmodel n = exists $ \_ -> path 1 n 0

path :: Int -> Int -> Int -> CSP' Int
path x y d
  | x == y = pure d
  | otherwise =
      disj
        [ dynamic
            ( fd_objective >>= \o ->
                pure (o @> (d + d' - 1) /\ (path z y (d + d')))
            )
        | (z, d') <- edge x
        ]

edge :: (Ord a, Num a, Num b) => a -> [(a, b)]
edge i
  | i < 400 = [(i + 1, 4), (i + 2, 1)]
  | otherwise = []

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
import Effects.Core ((:+:) (..), pattern Other)
import Effects.NonDet (NonDet (..))
import Effects.Solver (SolverE, runSolver, solve)
import Effects.Transformer (pattern InitT, pattern LeftT, pattern NextT, pattern RightT, pattern SolT)
import FD.OvertonFD (OvertonFD, fd_domain, fd_objective)
import Queens
import Solver (Solver (..))
import Prelude hiding (fail)
import Eval
import Transformers (rand, lds)

type Bound solver a =
  Free (CPSolve solver :+: NonDet :+: SolverE solver) a ->
  Free (CPSolve solver :+: NonDet :+: SolverE solver) a

type NewBound solver a = solver (Bound solver a)

data BBEvalState solver a = BBP Int (Bound solver a)

bb ::
  forall a solver.
  (Solver solver) =>
  NewBound solver a ->
  TransformerTree Int (BBEvalState solver a) solver a ->
  Free (SolverE solver) [a]
bb newBound = go
 where
  go ::
    TransformerTree Int (BBEvalState solver a) solver a -> Free (SolverE solver) [a]
  go (Pure a) = pure a
  go (InitT k) = go $ k 0 (BBP 0 id)
  go (SolT (BBP v _) k) = do
    bound' <- solve @solver $ newBound
    go $ k (BBP (v + 1) bound')
  go (LeftT ts k) = go $ k ts
  go (RightT ts k) = go $ k ts
  go (NextT tree v es@(BBP nv bound) k) =
    if nv > v
      then do
        let tree' = bound tree
         in go $ k tree' nv es
      else go $ k tree v es
  go (Other op) = Free $ go <$> op

bbSolve :: CSP' a -> [a]
bbSolve model = run . runSolver . (bb newBound) . (evalQ []) $ model

newBound :: forall a. NewBound OvertonFD a
newBound = do
  obj <- fd_objective
  dom <- fd_domain $ obj
  let val = head dom
  return ((\tree -> obj @< val /\ tree) :: Bound OvertonFD a)

bbBench :: Int -> Int -> Int -> [Int]
bbBench seed disc n = run . runSolver . (bb newBound) . (lds disc) . (rand seed) . (evalQ []) $ (gmodel n)

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

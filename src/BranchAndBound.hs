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
import Effects.CPSolve (CPSolve, dynamic, exists, (@<), (@>), pattern Add, pattern Dynamic, pattern NewVar)
import Effects.Core (Sub, (:+:) (..), pattern Other, pattern Other2)
import Effects.NonDet (NonDet (..), fail, try, pattern Fail, pattern (:|:))
import Effects.Solver (SolverE, solve, solveConstraints, runSolver)
import Effects.Transformer (TransformerE, initT, leftT, nextT, rightT, solT, pattern InitT, pattern LeftT, pattern NextT, pattern RightT, pattern SolT)
import FD.OvertonFD (OvertonFD, fd_domain, fd_objective)
import Handlers (it, traverseQ)
import Queens
import Queues
import Solver (Solver (..))
import Prelude hiding (fail)

evalQ ::
  forall solver sig q a es ts.
  (Solver solver, SolverE solver `Sub` sig, Queue q, Elem q ~ (Label solver, ts, Free (CPSolve solver :+: NonDet :+: sig) a)) =>
  q ->
  Free (CPSolve solver :+: NonDet :+: sig) a ->
  Free (TransformerE ts es (Free (CPSolve solver :+: NonDet :+: sig) a) :+: sig) [a]
evalQ queue model = initT (\ts es -> go queue model ts es)
  where
    go ::
      q ->
      Free (CPSolve solver :+: NonDet :+: sig) a ->
      ts ->
      es ->
      Free (TransformerE ts es (Free (CPSolve solver :+: NonDet :+: sig) a) :+: sig) [a]
    continue :: q -> es -> Free (TransformerE ts es (Free (CPSolve solver :+: NonDet :+: sig) a) :+: sig) [a]
    go q (Pure a) _ es = solT es (\es' -> (a :) <$> continue q es')
    go q (l :|: r) ts es = do
      now <- solve mark
      leftT ts $ \ls -> rightT ts $ \rs ->
        let q' = pushQ (now, ls, l) $ pushQ (now, rs, r) $ q
         in continue q' es
    go q (Fail) _ es = continue q es
    go q (Add c k) ts es = do
      success <- solve @solver $ addCons c
      if success then go q k ts es else continue q es
    go q (NewVar k) ts es = do
      var <- solve @solver $ newvar
      go q (k var) ts es
    go q (Dynamic k) ts es = do
      term <- solve @solver $ k
      go q term ts es
    go q (Other2 op) ts es = Free . Inr $ (\t -> go q t ts es) <$> op

    continue q es
      | nullQ q = pure []
      | otherwise =
          let ((now, ts, tree), q') = popQ q
           in do
                _ <- solve @solver $ goto now
                nextT tree ts es (go q')

testDumb :: CSP' a -> [a]
testDumb model = solveConstraints . it . (evalQ []) $ model

eval2 ::
  forall solver a sig.
  (Solver solver, NonDet `Sub` sig, SolverE solver `Sub` sig) =>
  Free (CPSolve solver :+: sig) a -> Free sig a
eval2 (Pure a) = pure $ a
eval2 (NewVar k) = do
  v <- solve @solver newvar
  eval2 (k v)
eval2 (Add c k) = do
  successful <- solve @solver $ addCons c
  if successful then eval2 k else fail
eval2 (Dynamic k) = do
  k' <- solve @solver $ k
  eval2 k'
eval2 (l :|: r) = do
  now <- solve @solver mark
  let l' = (solve @solver $ goto now) >>= const (eval2 l)
  let r' = (solve @solver $ goto now) >>= const (eval2 r)
  try l' r'
eval2 (Other f) = Free $ eval2 <$> f

testDumb2 :: CSP' a -> [a]
testDumb2 model = solveConstraints . it . (traverseQ []) . eval2 $ model

type Bound solver a =
  Free (CPSolve solver :+: NonDet :+: SolverE solver) a ->
  Free (CPSolve solver :+: NonDet :+: SolverE solver) a

type NewBound solver a = solver (Bound solver a)

data BBEvalState solver a = BBP Int (Bound solver a)

bb ::
  forall a solver.
  (Solver solver) =>
  NewBound solver a ->
  Free (TransformerE Int (BBEvalState solver a) (Free (CPSolve solver :+: NonDet :+: SolverE solver) a) :+: SolverE solver) [a] ->
  Free (SolverE solver) [a]
bb newBound = go
  where
    go ::
      Free (TransformerE Int (BBEvalState solver a) (Free (CPSolve solver :+: NonDet :+: SolverE solver) a) :+: SolverE solver) [a] ->
      Free (SolverE solver) [a]
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

----------------------------------------------------------

type CSP' a = Free (CPSolve OvertonFD :+: NonDet :+: SolverE OvertonFD) a

gmodel :: Int -> CSP' Int
gmodel n = exists @OvertonFD $ \_ -> path 1 n 0

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
  | i < 20 = [(i + 1, 4), (i + 2, 1)]
  | otherwise = []

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Eval where

import Control.Monad.Free (Free (..))
import Effects.Algebra
import Effects.CPSolve (CPSolve (..), pattern Add, pattern Dynamic, pattern NewVar)
import Effects.Core ((:+:) (..), pattern Other2)
import Effects.NonDet (NonDet (..), pattern Fail, pattern (:|:))
import Effects.Solver (SolverE, runSolver, solve)
import Effects.Transformer (TransformerE (..), initT, leftS, nextT, rightS, solT)
import FD.OvertonFD (OvertonFD)
import Queues (Queue (..))
import Solver (Solver (..))
import Prelude hiding (fail)

type SearchTree solver a = Free (CPSolve solver :+: NonDet :+: SolverE solver) a
type TransformerTree ts es solver a b = Free (TransformerE ts es (SearchTree solver a) :+: SolverE solver) b
type CSP a = SearchTree OvertonFD a

dfs ::
  (Solver solver) =>
  (TransformerTree ts es solver a [a] -> Free (SolverE solver) [a]) ->
  SearchTree solver a ->
  [a]
dfs trans model = run . runSolver . trans . (flip eval []) $ model

dfsO ::
  (Solver solver) =>
  (TransformerTree ts es solver a [a] -> Free (SolverE solver) [a]) ->
  SearchTree solver a ->
  [a]
dfsO trans model = run . runSolver . trans . (evalQ []) $ model

eval ::
  forall solver q a es ts.
  (Solver solver, Queue q, Elem q ~ (Label solver, ts, SearchTree solver a)) =>
  SearchTree solver a ->
  q ->
  TransformerTree ts es solver a [a]
eval model queue = initT (\ts es -> go model ts es queue)
 where
  go :: SearchTree solver a -> ts -> es -> q -> TransformerTree ts es solver a [a]
  go = handlePara (liftPara algCP <| algNonDet <| liftPara conCSP) genCSP

  genCSP a _ es q = solT es (\es' -> (a :) <$> continue q es')

  algCP (Add' c k) ts es q = do
    success <- solve $ addCons c
    if success then k ts es q else continue q es
  algCP (NewVar' k) ts es q = do
    var <- solve newvar
    k var ts es q
  algCP (Dynamic' d) ts es q = do
    k <- solve d
    k ts es q

  algNonDet (Try' (l, _) (r, _)) ts es q = do
    now <- solve mark
    ls <- leftS ts
    rs <- rightS ts
    let q' = pushQ (now, ls, l) $ pushQ (now, rs, r) $ q
    continue q' es
  algNonDet (Fail') _ es q = continue q es

  conCSP op q ts es = Free . Inr $ (\f -> f q ts es) <$> op

  continue :: q -> es -> TransformerTree ts es solver a [a]
  continue q es
    | nullQ q = pure []
    | otherwise =
        let ((now, ts, tree), q') = popQ q
         in do
              solve $ goto now
              nextT tree ts es (\tree' ts' es' -> go tree' ts' es' q')

evalQ ::
  forall solver q a es ts.
  (Solver solver, Queue q, Elem q ~ (Label solver, ts, SearchTree solver a)) =>
  q ->
  SearchTree solver a ->
  TransformerTree ts es solver a [a]
evalQ queue model = initT (\ts es -> go model queue ts es)
 where
  go :: SearchTree solver a -> q -> ts -> es -> TransformerTree ts es solver a [a]
  continue :: q -> es -> TransformerTree ts es solver a [a]

  go (Pure a) q _ es = solT es (\es' -> (a :) <$> continue q es')
  go (l :|: r) q ts es = do
    now <- solve mark
    ls <- leftS ts
    rs <- rightS ts
    let q' = pushQ (now, ls, l) $ pushQ (now, rs, r) $ q
    continue q' es
  go (Fail) q _ es = continue q es
  go (Add c k) q ts es = do
    success <- solve $ addCons c
    if success then go k q ts es else continue q es
  go (NewVar k) q ts es = do
    var <- solve newvar
    go (k var) q ts es
  go (Dynamic k) q ts es = do
    term <- solve k
    go term q ts es
  go (Other2 op) q ts es = Free . Inr $ (\t -> go t q ts es) <$> op
  go (Free _) _ _ _ = undefined

  continue q es
    | nullQ q = pure []
    | otherwise =
        let ((now, ts, tree), q') = popQ q
         in do
              solve $ goto now
              nextT tree ts es (\tree' ts' es' -> go tree' q' ts' es')

-- evalIndep ::
--   forall solver a sig.
--   (Solver solver, NonDet `Sub` sig, SolverE solver `Sub` sig) =>
--   Free (CPSolve solver :+: sig) a -> Free sig a
-- evalIndep (Pure a) = pure $ a
-- evalIndep (NewVar k) = do
--   v <- solve newvar
--   evalIndep (k v)
-- evalIndep (Add c k) = do
--   successful <- solve $ addCons c
--   if successful then evalIndep k else fail
-- evalIndep (Dynamic k) = do
--   k' <- solve $ k
--   evalIndep k'
-- evalIndep (l :|: r) = do
--   now <- solve @solver mark
--   let l' = (solve $ goto now) >> evalIndep l
--   let r' = (solve $ goto now) >> evalIndep r
--   try l' r'
-- evalIndep (Other f) = Free $ evalIndep <$> f
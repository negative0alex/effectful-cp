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
import Effects.CPSolve (CPSolve (..))
import Effects.Core ((:+:) (..))
import Effects.NonDet (NonDet (..), pattern (:|:))
import Effects.Solver (SolverE, solve)
import Effects.Transformer (TransformerE (..), initT, leftS, nextT, rightS, solT)
import FD.OvertonFD (OvertonFD)
import Queues (Queue (..))
import Solver (Solver (..))
import Prelude hiding (fail)

type SearchTree solver a = Free (CPSolve solver :+: NonDet :+: SolverE solver) a
type TransformerTree ts es solver a b = Free (TransformerE ts es (SearchTree solver a) :+: SolverE solver) b
type CSP a = Free (CPSolve OvertonFD :+: NonDet :+: SolverE OvertonFD) a

eval ::
  forall solver q a es ts.
  (Solver solver, Queue q, Elem q ~ (Label solver, ts, SearchTree solver a)) =>
  q ->
  SearchTree solver a ->
  TransformerTree ts es solver a [a]
eval queue model = initT (\ts es -> go model queue ts es)
 where
  go :: SearchTree solver a -> q -> ts -> es -> TransformerTree ts es solver a [a]
  continue :: q -> es -> TransformerTree ts es solver a [a]
  go = handlePara (liftPara algCP <|| algNonDet <|| liftPara conCSP) genCSP

  genCSP a q _ es = solT es (\es' -> (a :) <$> continue q es')

  algCP (Add' c k) q ts es = do
    success <- solve $ addCons c
    if success then k q ts es else continue q es
  algCP (NewVar' k) q ts es = do
    var <- solve newvar
    k var q ts es
  algCP (Dynamic' d) q ts es = do
    k <- solve d
    k q ts es

  algNonDet ::
    SearchTree solver a ->
    NonDet (q -> ts -> es -> TransformerTree ts es solver a [a]) ->
    q ->
    ts ->
    es ->
    TransformerTree ts es solver a [a]
  algNonDet (l :|: r) (Try' _ _) q ts es = do
    now <- solve mark
    ls <- leftS ts
    rs <- rightS ts
    let q' = pushQ (now, ls, l) $ pushQ (now, rs, r) $ q
    continue q' es
  algNonDet _ (Fail') q _ es = continue q es

  conCSP op q ts es = Free . Inr $ (\f -> f q ts es) <$> op

  continue q es
    | nullQ q = pure []
    | otherwise =
        let ((now, ts, tree), q') = popQ q
         in do
              solve $ goto now
              nextT tree ts es (\tree' ts' es' -> go tree' q' ts' es')


-- evalQ ::
--   forall solver q a es ts.
--   (Solver solver, Queue q, Elem q ~ (Label solver, ts, SearchTree solver a)) =>
--   q ->
--   SearchTree solver a ->
--   TransformerTree ts es solver a [a]
-- evalQ queue model = initT (\ts es -> go model queue ts es)
--  where
--   go :: SearchTree solver a -> q -> ts -> es -> TransformerTree ts es solver a [a]
--   continue :: q -> es -> TransformerTree ts es solver a [a]

--   go (Pure a) q _ es = solT es (\es' -> (a :) <$> continue q es')
--   go (l :|: r) q ts es = do
--     now <- solve mark
--     ls <- leftS ts
--     rs <- rightS ts
--     let q' = pushQ (now, ls, l) $ pushQ (now, rs, r) $ q
--     continue q' es
--   go (Fail) q _ es = continue q es
--   go (Add c k) q ts es = do
--     success <- solve $ addCons c
--     if success then go k q ts es else continue q es
--   go (NewVar k) q ts es = do
--     var <- solve newvar
--     go (k var) q ts es
--   go (Dynamic k) q ts es = do
--     term <- solve k
--     go term q ts es
--   go (Other2 op) q ts es = Free . Inr $ (\t -> go t q ts es) <$> op
--   go (Free _) _ _ _ = undefined

--   continue q es
--     | nullQ q = pure []
--     | otherwise =
--         let ((now, ts, tree), q') = popQ q
--          in do
--               solve $ goto now
--               nextT tree ts es (\tree' ts' es' -> go tree' q' ts' es')


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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Handlers where

import Control.Monad (liftM2)
import Control.Monad.Free (Free (..), MonadFree (wrap))
import Data.Sequence (Seq)
import Effects.CPSolve (CPSolve, pattern Add, pattern Dynamic, pattern NewVar)
import Effects.Core (Sub (..), Void, runEffects, (:+:) (..), pattern Other)
import Effects.NonDet (NonDet (..), fail, try, pattern Fail, pattern (:|:))
import Effects.Transformer (TransformerE, initT, leftT, nextT, rightT, solT, pattern InitT, pattern LeftT, pattern NextT, pattern RightT, pattern SolT)
import Queues (Queue (..))
import Solver (Solver (..))
import System.Random
import Prelude hiding (fail)

eval ::
  (Solver solver, NonDet `Sub` sig, Traversable sig) =>
  Free (CPSolve solver :+: sig) a -> solver (Free sig a)
eval (Pure a) = pure . pure $ a
eval (NewVar k) = do
  v <- newvar
  eval (k v)
eval (Add c k) = do
  successful <- addCons c
  if successful then eval k else pure fail
eval (Dynamic k) = k >>= eval
eval (l :|: r) = do
  now <- mark
  l' <- eval l
  goto now
  r' <- eval r
  goto now
  pure $ try l' r'
eval (Fail) = pure fail
eval (Other f) = Free <$> traverse eval f

allSols :: (Functor sig) => Free (NonDet :+: sig) a -> Free sig [a]
allSols (Pure a) = pure [a]
allSols (l :|: r) = liftM2 (++) (allSols l) (allSols r)
allSols Fail = pure []
allSols (Other f) = Free (allSols <$> f)

solve1 :: (Solver solver) => Free (CPSolve solver :+: NonDet :+: Void) a -> [a]
solve1 model = run $ runEffects . allSols <$> eval model

solve1DBS model = run $ runEffects . allSols . (dbsH 5) <$> eval model

traverseQ ::
  forall sig a q ts es.
  (Queue q, Elem q ~ (ts, Free (NonDet :+: sig) a), Functor sig) =>
  q ->
  Free (NonDet :+: sig) a ->
  Free (TransformerE ts es (Free (NonDet :+: sig) a) :+: sig) [a]
traverseQ queue model = initT (\tsInit esInit -> go queue model tsInit esInit)
  where
    go :: q -> Free (NonDet :+: sig) a -> ts -> es -> Free (TransformerE ts es (Free (NonDet :+: sig) a) :+: sig) [a]
    go q (Pure a) _ es = solT es (\es' -> (a :) <$> continue q es')
    go q (l :|: r) ts es =
      leftT
        ts
        ( \ls ->
            rightT
              ts
              ( \rs ->
                  let q' = pushQ (ls, l) $ pushQ (rs, r) $ q
                   in continue q' es
              )
        )
    go q (Fail) _ es = continue q es
    go q (Other op) ts es = Free . Inr $ (\t -> go q t ts es) <$> op
    continue :: q -> es -> Free (TransformerE ts es (Free (NonDet :+: sig) a) :+: sig) [a]
    continue q es
      | nullQ q = pure []
      | otherwise =
          let ((ts, tree), q') = popQ q
           in nextT tree ts es (go q')

traverseQ' ::
  (Queue q, Elem q ~ (Free (NonDet :+: sig) a), Functor sig) =>
  q -> Free (NonDet :+: sig) a -> Free (sig) [a]
traverseQ' = go
  where
    go q (Pure a) = (a :) <$> continue q
    go q (l :|: r) = continue (pushQ l $ pushQ r q)
    go q Fail = continue q
    continue q
      | nullQ q = pure []
      | otherwise =
          let (tree, q') = popQ q
           in go q' tree

it :: forall el a sig. (Functor sig) => Free (TransformerE () () el :+: sig) [a] -> Free sig [a]
it (SolT _ k) = it $ k ()
it (InitT k) = it $ k () ()
it (LeftT _ k) = it $ k ()
it (RightT _ k) = it (k ())
it (NextT x _ _ k) = it $ k x () ()
it (Pure a) = pure a
it (Other op) = wrap (it <$> op)

type CTransformer ts es =
  forall a tsRest esRest sig.
  (Functor sig) =>
  Free (TransformerE (ts, tsRest) (es, esRest) (Free (NonDet :+: sig) a) :+: sig) [a] ->
  Free (TransformerE tsRest esRest (Free (NonDet :+: sig) a) :+: sig) [a]

makeT ::
  forall ts es a tsRest esRest sig.
  (Functor sig) =>
  ts ->
  es ->
  (es -> es) ->
  (ts -> ts) ->
  (ts -> ts) ->
  (ts -> es -> Free (NonDet :+: sig) a -> (ts, es, Free (NonDet :+: sig) a)) ->
  ( Free (TransformerE (ts, tsRest) (es, esRest) (Free (NonDet :+: sig) a) :+: sig) [a] ->
    Free (TransformerE tsRest esRest (Free (NonDet :+: sig) a) :+: sig) [a]
  )
makeT tsInit esInit solEs leftTs rightTs nextState = go
  where
    go ::
      Free (TransformerE (ts, tsRest) (es, esRest) (Free (NonDet :+: sig) a) :+: sig) [a] ->
      Free (TransformerE tsRest esRest (Free (NonDet :+: sig) a) :+: sig) [a]
    go (InitT k) = initT (\tsRest esRest -> go $ k (tsInit, tsRest) (esInit, esRest))
    go (SolT (es, esRest) k) = solT esRest (\esRest' -> go $ k (solEs es, esRest'))
    go (LeftT (ts, tsRest) k) = leftT tsRest (\tsRest' -> go $ k (leftTs ts, tsRest'))
    go (RightT (ts, tsRest) k) = rightT tsRest (\tsRest' -> go $ k (rightTs ts, tsRest'))
    go (NextT tree (ts, tsRest) (es, esRest) k) =
      let (ts', es', tree') = nextState ts es tree
       in nextT tree' tsRest esRest (\tree'' tsRest' esRest' -> go $ k tree'' (ts', tsRest') (es', esRest'))
    go (Pure a) = pure a
    go (Other op) = wrap $ Inr (go <$> op)

fsC :: CTransformer () Bool
fsC =
  makeT
    ()
    True
    (const False)
    id
    id
    (\_ keepGoing tree -> if keepGoing then ((), keepGoing, tree) else ((), keepGoing, fail))

dbsC :: Int -> CTransformer Int ()
dbsC depthLimit = makeT 0 () id succ succ (\depth _ tree -> (depth, (), if depth <= depthLimit then tree else fail))

nbsC :: Int -> CTransformer () Int
nbsC nodeLimit = makeT () 0 id id id (\_ nodes tree -> ((), nodes + 1, if nodes <= nodeLimit then tree else fail))

ldsC :: Int -> CTransformer Int ()
ldsC discrepancy = makeT 0 () id id succ (\disc _ tree -> (disc, (), if disc <= discrepancy then tree else fail))

flipT :: (NonDet `Sub` sig) => Free sig a -> Free sig a
flipT (l :|: r) = try r l
flipT other = other

randC :: Int -> CTransformer () [Bool]
randC seed =
  makeT
    ()
    (randoms $ mkStdGen seed)
    id
    id
    id
    (\_u coins tree -> ((), tail coins, if head coins then flipT tree else tree))

exampleTrans :: Int -> Int -> Int -> CTransformer Int ([Bool], Int)
exampleTrans nodeLimit seed depthLimit =
  makeT
    0
    (randoms $ mkStdGen seed, 0)
    id
    succ
    succ
    ( \depth es tree ->
        let (coins, nodes) = es
         in ( depth,
              (tail coins, nodes + 1),
              if depth <= depthLimit && nodes <= nodeLimit
                then
                  (if head coins then flipT tree else tree)
                else fail
            )
    )

exampleIt ::
  forall sig a.
  (Functor sig) =>
  Int ->
  Int ->
  Int ->
  Free (TransformerE Int ([Bool], Int) (Free (NonDet :+: sig) a) :+: sig) [a] ->
  Free sig [a]
exampleIt nodeLimit seed depthLimit = go
  where
    go :: Free (TransformerE Int ([Bool], Int) (Free (NonDet :+: sig) a) :+: sig) [a] -> Free sig [a]
    go (InitT k) = go (k 0 (randoms $ mkStdGen seed, 0))
    go (SolT es k) = go (k es)
    go (LeftT ts k) = go (k (ts + 1))
    go (RightT ts k) = go (k (ts + 1))
    go (NextT tree ts es k) =
      let (coins, nodes) = es
       in go (k 
       (if ts <= depthLimit && nodes <= nodeLimit then (if head coins then flipT tree else tree) else fail) 
       ts (tail coins, nodes + 1))
    go (Pure a) = pure a
    go (Other f) = Free $ (go <$> f)


----------------------------------- Testing

testExample :: (Solver solver) => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testExample model = run $ runEffects . it . (nbsC 1500) . (randC 300) . (dbsC 15) . (traverseQ []) <$> eval model

testBigExample :: (Solver solver) => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testBigExample model = run $ runEffects . it . (nbsC 18000) . (randC 300) . (dbsC 25) . (traverseQ []) <$> eval model

testBigFusedExample :: (Solver solver) => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testBigFusedExample model = run $ runEffects . it . (exampleTrans 18000 300 25) . (traverseQ []) <$> eval model

testExampleIt :: (Solver solver) => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a] 
testExampleIt model = run $ runEffects . (exampleIt 18000 300 25) . (traverseQ []) <$> eval model

-- λ| length $ testExample 15 1500 (nqueens 8)
-- 31

-- big example : 10 queens, nodes 18000, seed 300, depth 25

testRand :: (Solver solver) => Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testRand seed model = run $ runEffects . it . (randC seed) . (traverseQ []) <$> eval model

testRandDbs :: (Solver solver) => Int -> Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testRandDbs seed depth model = run $ runEffects . it . (randC seed) . (dbsC depth) . (traverseQ []) <$> eval model

testDbs :: (Solver solver) => Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testDbs depth model = run $ runEffects . it . (dbsC depth) . (traverseQ []) <$> eval model

testNbs :: (Solver solver) => Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testNbs nodes model = run $ runEffects . it . (nbsC nodes) . (traverseQ []) <$> eval model

testLds :: (Solver solver) => Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testLds disc model = run $ runEffects . it . (ldsC disc) . (traverseQ []) <$> eval model

testDbsBfs :: (Solver solver) => Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testDbsBfs nodes model = run $ runEffects . it . (dbsC nodes) . (traverseQ (emptyQ :: Seq a)) <$> eval model

testIt :: (Solver solver) => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testIt model = run $ runEffects . it . (traverseQ []) <$> eval model

testItBfs :: (Solver solver) => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testItBfs model = run $ runEffects . it . (traverseQ (emptyQ :: Seq a)) <$> eval model

testFs :: (Solver solver) => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testFs model = run $ runEffects . it . fsC . (traverseQ []) <$> eval model

testNbsDbs :: (Solver solver) => Int -> Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testNbsDbs nodes depth model = run $ runEffects . it . (nbsC nodes) . (dbsC depth) . (traverseQ []) <$> eval model

testLdsNbsDbs :: (Solver solver) => Int -> Int -> Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testLdsNbsDbs disc nodes depth model =
  run $ runEffects . it . (ldsC disc) . (nbsC nodes) . (dbsC depth) . (traverseQ []) <$> eval model

naiveSols :: forall solver a. (Solver solver) => Free (CPSolve solver :+: NonDet :+: Void) a -> solver [a]
naiveSols = go
  where
    go (Pure a) = pure [a]
    go (NewVar k) = do
      v <- newvar
      go (k v)
    go (Add c k) = do
      successful <- addCons c
      if successful then go k else pure []
    go (Dynamic k) = do
      term <- k
      go term
    go (l :|: r) = do
      now <- mark
      l' <- go l
      goto now
      r' <- go r
      pure $ l' <> r'
    go (Fail) = pure []

testNaive :: forall solver a. (Solver solver) => Free (CPSolve solver :+: NonDet :+: Void) a -> [a]
testNaive = run . naiveSols

-- ------------------------
dbsH :: forall sig a. (NonDet `Sub` sig) => Int -> Free sig a -> Free sig a
dbsH depthLimit = go 0 -- initial depth is 0
  where
    go :: Int -> Free sig a -> Free sig a
    go depth (Pure a) = if depth <= depthLimit then pure a else fail
    -- increment depth for each branch
    go depth (l :|: r) = try (go (depth + 1) l) (go (depth + 1) r)
    go depth (Free f) = Free $ (go depth) <$> f


dbsT ::
  forall sig a.
  (Functor sig) =>
  Int ->
  Free (TransformerE Int () (Free (NonDet :+: sig) a) :+: sig) [a] ->
  Free sig [a]
dbsT depthLimit = go
  where
    go :: Free (TransformerE Int () (Free (NonDet :+: sig) a) :+: sig) [a] -> Free sig [a]
    go (InitT k) = go (k 0 ())
    go (SolT es k) = go (k es)
    go (LeftT ts k) = go (k (ts + 1))
    go (RightT ts k) = go (k (ts + 1))
    go (NextT tree ts es k) = go (k (if ts <= depthLimit then tree else fail) ts es)
    go (Pure a) = pure a
    go (Other f) = Free $ (go <$> f)

nbsT ::
  forall sig a.
  (Functor sig) =>
  Int ->
  Free (TransformerE () Int (Free (NonDet :+: sig) a) :+: sig) [a] ->
  Free sig [a]
nbsT nodeLimit = go
  where
    go :: Free (TransformerE () Int (Free (NonDet :+: sig) a) :+: sig) [a] -> Free sig [a]
    go (InitT k) = go (k () 0)
    go (SolT es k) = go (k es)
    go (LeftT ts k) = go (k ts)
    go (RightT ts k) = go (k ts)
    go (NextT tree ts es k) = go (k (if es <= nodeLimit then tree else fail) ts (es + 1))
    go (Pure a) = pure a
    go (Other f) = Free $ (go <$> f)

dbsAndNbsT ::
  forall sig a.
  (Functor sig) =>
  Int ->
  Int ->
  Free (TransformerE Int Int (Free (NonDet :+: sig) a) :+: sig) [a] ->
  Free sig [a]
dbsAndNbsT depthLimit nodeLimit = go
  where
    go :: Free (TransformerE Int Int (Free (NonDet :+: sig) a) :+: sig) [a] -> Free sig [a]
    go (InitT k) = go (k 0 0)
    go (SolT es k) = go (k es)
    go (LeftT ts k) = go (k (ts + 1))
    go (RightT ts k) = go (k (ts + 1))
    go (NextT tree ts es k) = go (k (if ts <= depthLimit && es <= nodeLimit then tree else fail) ts (es + 1))
    go (Pure a) = pure a
    go (Other f) = Free $ (go <$> f)


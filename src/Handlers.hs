{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Handlers where

import CPSolve (CPSolve, pattern Add, pattern Dynamic, pattern NewVar)
import Control.Monad.Free (Free (..), MonadFree (wrap))
import Data.Sequence (Seq)
import Effects (Sub (..), Void, runEffects, (:+:) (..), pattern Other)
import NonDet (NonDet (..), fail, try, pattern Fail, pattern (:|:))
import Queues (Queue (..))
import Solver (Solver (..))
import Transformer (TransformerE, initT, leftT, nextT, rightT, solT, pattern InitT, pattern LeftT, pattern NextT, pattern RightT, pattern SolT)
import Prelude hiding (fail)

eval ::
  forall solver a sig.
  (Solver solver, NonDet `Sub` sig) =>
  Free (CPSolve solver :+: sig) a ->
  solver (Free sig a)
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

traverseQ ::
  forall sig a q ts es.
  (Queue q, Elem q ~ (ts, Free (NonDet :+: sig) a), Functor sig) =>
  q ->
  Free (NonDet :+: sig) a ->
  Free (TransformerE ts es (Free (NonDet :+: sig) a) :+: sig) [a]
traverseQ queue model = initT (\tsInit esInit -> go queue model tsInit esInit)
  where
    go :: q -> Free (NonDet :+: sig) a -> ts -> es -> Free (TransformerE ts es (Free (NonDet :+: sig) a) :+: sig) [a]
    -- go q (Pure a) _ es    = (a:) <$> continue q es
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
    continue :: q -> es -> Free (TransformerE ts es (Free (NonDet :+: sig) a) :+: sig) [a]
    continue q es
      | nullQ q = pure []
      | otherwise = do
          let ((ts, tree), q') = popQ q
          nextT tree ts es (\tree' ts' es' -> go q' tree' ts' es')



it :: forall el a sig. (Functor sig) => Free (TransformerE () () el :+: sig) [a] -> Free sig [a]
it (SolT _ k) = it $ k ()
it (InitT k) = it $ k () ()
it (LeftT _ k) = it $ k ()
it (RightT _ k) = it (k ())
it (NextT x _ _ k) = it $ k x () ()
it (Pure a) = pure a
it (Other op) = wrap (it <$> op)



type CTransformer ts es =
  forall a tsRest esRest sig. (Functor sig) =>
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

----------------------------------- Testing

testDbs :: (Solver solver) => Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testDbs depth model = run $ runEffects . it . (dbsC depth) . (traverseQ []) <$> eval model

testNbs :: (Solver solver) => Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testNbs nodes model = run $ runEffects . it . (nbsC nodes) . (traverseQ []) <$> eval model

testNbs' :: (Solver solver) => Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testNbs' nodes model = run $ runEffects . it . (nbsC nodes) . (traverseQ []) <$> eval model

testDbsBfs :: (Solver solver) => Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testDbsBfs nodes model = run $ runEffects . it . (dbsC nodes) . (traverseQ (emptyQ :: Seq a)) <$> eval model

testIt :: Solver solver => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testIt model = run $ runEffects . it . (traverseQ []) <$> eval model

testItBfs :: Solver solver => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testItBfs model = run $ runEffects . it . (traverseQ (emptyQ :: Seq a)) <$> eval model

testFs :: Solver solver => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testFs model = run $ runEffects . it . fsC . (traverseQ []) <$> eval model

naiveAllSols :: forall solver a. (Solver solver) => Free (CPSolve solver :+: NonDet :+: Void) a -> solver [a]
naiveAllSols = go 
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
testNaive = run . naiveAllSols
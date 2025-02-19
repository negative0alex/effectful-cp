{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Handlers where
import NonDet (NonDet (..), pattern Fail, pattern (:|:), fail, try)
import SplitCPEffects (Sub (..), (:+:) (..), pattern Other, Void, runEffects, getRUnsafe)
import Control.Monad.Free (Free (..))
import Control.Monad (liftM2)
import Prelude hiding (fail)
import Solver (Solver (..))
import CPSolve (CPSolve, pattern NewVar, pattern Add, pattern Dynamic)
import Queues (QueueE, pop, push, Queue (..), pattern Push, pattern Pop)
import Data.Sequence (Seq)
import Transformer (TransformerE, leftT, rightT, nextT, initT, pattern LeftT, pattern RightT, pattern NextT, pattern InitT)

naiveAllSols :: Functor sig => Free (NonDet :+: sig) a -> Free sig [a]
naiveAllSols (Pure a)   = pure [a]
naiveAllSols Fail       = pure []
naiveAllSols (a :|: b)  = liftM2 (<>) (naiveAllSols a) (naiveAllSols b)
naiveAllSols (Other op) = Free (fmap naiveAllSols op)


knapsack :: Int -> [Int] -> Free (NonDet :+: Void) [Int]
knapsack w vs
  | w < 0  = fail
  | w == 0 = pure []
  | otherwise  = do
    v <- select vs
    vs' <- knapsack (w-v) vs
    pure (v:vs')
  where
    select = foldr (try . pure) fail


eval :: forall solver a. (Solver solver) =>
  Free (CPSolve solver :+: NonDet :+: Void) a -> solver (Free (NonDet :+: Void) a)
eval (Pure a)    = pure . pure $ a
eval (NewVar k)  = do
  v <- newvar 
  eval (k v)
eval (Add c k)   = do 
  successful <- addCons c 
  if successful then eval k else pure fail
eval (Dynamic k) = k >>= eval
eval (l :|: r)   = do 
  now <- mark 
  l' <- eval l 
  goto now 
  r' <- eval r 
  goto now 
  pure $ try l' r'
eval (Fail)      = pure fail

dbs :: forall sig a. (NonDet `Sub` sig) => Int -> Free sig a -> Free sig a 
dbs depthBudget (l :|: r) = if depthBudget > 0 then try (dbs (depthBudget - 1) l) (dbs (depthBudget - 1) r) else fail 
dbs _ (Pure x) = pure x 
dbs depthBudget (Free op) = Free $ dbs depthBudget <$> op



queueify :: forall sig a. (Functor sig) =>
  Free (NonDet :+: sig) a -> Free (QueueE (Free (NonDet :+: sig) a) :+: sig) a 
queueify (Fail) = pop 
queueify (l :|: r) = push r $ push l $ pop 
queueify (Pure x) = pure x 
-- queueify (Free op) = Free . Inr $ queueify <$> op
queueify (Free op) = Free . Inr $ queueify <$> getRUnsafe op

traverseQueue :: forall sig a q. (Queue q, Elem q~ (Free (NonDet :+: sig) a), Functor sig) =>
  q -> Free (QueueE (Free (NonDet :+: sig) a) :+: sig) a -> Free sig [a]
traverseQueue = go 
  where 
    go :: q -> Free (QueueE (Free (NonDet :+: sig) a) :+: sig) a -> Free sig [a]
    go wl (Pure x) = (x:) <$> continue wl 
    go wl (Pop)  = continue wl 
    go wl (Push i k) = go (pushQ i wl) k 
    continue :: q  -> Free sig [a]
    continue wl
      | nullQ wl  = pure []
      | otherwise =
        let (t, wl') = popQ wl
        in go wl' (queueify t) 

solveNaive :: Solver solver => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
solveNaive model = run $ runEffects . naiveAllSols <$> eval model
solveDFS :: Solver solver => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
solveDFS model = run $ runEffects . traverseQueue [] . queueify <$> eval model
solveBFS :: Solver solver => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
solveBFS model = run $ runEffects . traverseQueue (emptyQ :: Seq a) . queueify <$> eval model


traverseQ :: forall sig a q ts es. (Queue q, Elem q~ (ts, Free (NonDet :+: sig) a), Functor sig) =>
  q -> Free (NonDet :+: sig) a -> ts -> es -> Free (TransformerE ts es (Free (NonDet :+: sig) a) :+: sig) [a]
traverseQ  = go
  where 
  go :: q -> Free (NonDet :+: sig) a -> ts -> es -> Free (TransformerE ts es (Free (NonDet :+: sig) a) :+: sig) [a]
  go q (Pure a) _ es    = (a:) <$> continue q es
  go q (l :|: r) ts es = leftT ts (\ls -> rightT ts (\rs -> 
    let q' = pushQ (ls, l) $ pushQ (rs, r) $ q in 
    continue q' es
    ))
  go q (Fail) _ es    = continue q es
  continue :: q -> es -> Free (TransformerE ts es (Free (NonDet :+: sig) a) :+: sig) [a]
  continue q es 
    | nullQ q   = pure []
    | otherwise = do
      let ((ts, tree), q') = popQ q 
      nextT tree ts es (\tree' ts' es' -> traverseQ q' tree' ts' es')


dbs' :: forall a. 
  Int -> Free (TransformerE Int () (Free (NonDet :+: Void) a) :+: Void) [a] ->
    Free (Void) [a]
dbs' depth_limit = go 
  where 
    go :: Free (TransformerE Int () (Free (NonDet :+: Void) a) :+: Void) [a] ->
      Free (Void) [a]
    go (LeftT ts k)  = go $ k (ts+1)
    go (RightT ts k) = go (leftT ts k)
    go (NextT x ts _ k) = if ts <= depth_limit then go $ k x ts () else go $ k fail ts ()
    go (Pure as) = pure as

nbs :: forall a. 
  Int -> Free (TransformerE () Int (Free (NonDet :+: Void) a) :+: Void) [a] -> Free Void [a]
nbs node_limit = go 
  where 
    go :: Free (TransformerE () Int (Free (NonDet :+: Void) a) :+: Void) [a] -> Free Void [a]
    go (LeftT  _ k) = go $ k ()
    go (RightT _ k) = go $ k ()
    go (NextT x _ es k) = if es <= node_limit then go $ k x () (es + 1) else go $ k fail () es 
    go (Pure a) = pure a 


dbs_comp_bad :: forall a ts_other es_other. 
  Int -> ts_other -> es_other -> Free (TransformerE Int () (Free (NonDet :+: Void) a) :+: Void) [a] ->
    Free (TransformerE ts_other es_other (Free (NonDet :+: Void) a) :+: Void) [a]
dbs_comp_bad depth_limit = go 
  where 
    go :: ts_other -> es_other -> Free (TransformerE Int () (Free (NonDet :+: Void) a) :+: Void) [a] ->
      Free (TransformerE ts_other es_other (Free (NonDet :+: Void) a) :+: Void) [a]

    go ts_other es_other (LeftT ts k) = leftT ts_other (\ts_other' -> go ts_other' es_other (k (ts+1))) 

    go ts_other es_other (RightT ts k) = go ts_other es_other (leftT ts k)

    go ts_other es_other (NextT x ts _ k) = if ts <= depth_limit then
      nextT x ts_other es_other (\x' ts_other' es_other' -> go ts_other' es_other' $ k x' ts ()) else
        nextT fail ts_other es_other (\x' ts_other' es_other' -> go ts_other' es_other' $ k x' ts ())

    go _ _ (Pure a) = pure a

it :: (Functor sig) => Free (TransformerE () () (Free (NonDet :+: Void) a) :+: sig) [a] -> Free Void [a] 
it (LeftT _ k)  = it $ k ()
it (RightT _ k) = it (k ())
it (NextT x _ _ k) = it $ k x () ()
it (Pure a) = pure a

solve model = run $ runEffects . it . (\m -> traverseQ [] m () ()) <$> eval model

dbs_once depth model = run $ runEffects . (dbs' depth) . (\m -> traverseQ [] m 0 ()) <$> eval model

dbs_comp :: forall a tsRest esRest. 
  Int  -> Free (TransformerE (Int, tsRest) ((), esRest) (Free (NonDet :+: Void) a) :+: Void) [a] ->
    Free (TransformerE tsRest esRest (Free (NonDet :+: Void) a) :+: Void) [a]
dbs_comp depthLimit = go 
  where 
    go :: Free (TransformerE (Int, tsRest) ((), esRest) (Free (NonDet :+: Void) a) :+: Void) [a] ->
      Free (TransformerE tsRest esRest (Free (NonDet :+: Void) a) :+: Void) [a]
    go (LeftT  (depth, tsRest) k) = leftT  tsRest (\tsRest' -> go $ k (depth+1, tsRest'))
    go (RightT (depth, tsRest) k) = rightT tsRest (\tsRest' -> go $ k (depth+1, tsRest'))
    go (NextT tree (depth, tsRest) (_, esRest) k) = nextT tree tsRest esRest (\tree' tsRest' esRest' -> 
      if depth <= depthLimit then go $ k tree' (depth, tsRest') ((), esRest') else go $ k fail (depth, tsRest') ((), esRest'))
    go (Pure a) = pure a

test_dbs :: Solver solver => Int -> Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
test_dbs depthOuter depthInner model = run $ runEffects . it . (dbs_comp depthOuter) . (dbs_comp depthInner) .
  (\m -> traverseQ [] m (0,(0,())) ((), ((), ()))) <$> eval model
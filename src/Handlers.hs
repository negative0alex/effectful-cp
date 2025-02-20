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
import SplitCPEffects (Sub (..), (:+:) (..), pattern Other, Void, runEffects)
import Control.Monad.Free (Free (..))
import Prelude hiding (fail)
import Solver (Solver (..))
import CPSolve (CPSolve, pattern NewVar, pattern Add, pattern Dynamic)
import Queues (Queue (..))
import Transformer (TransformerE, leftT, rightT, nextT, initT, pattern LeftT, pattern RightT, pattern NextT, pattern InitT)



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


eval :: forall solver a sig. (Solver solver, NonDet `Sub` sig) =>
  Free (CPSolve solver :+: sig) a -> solver (Free sig a)
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


traverseQ :: forall sig a q ts es. (Queue q, Elem q~ (ts, Free (NonDet :+: sig) a), Functor sig) =>
  q -> Free (NonDet :+: sig) a -> Free (TransformerE ts es (Free (NonDet :+: sig) a) :+: sig) [a]
traverseQ  queue model = initT (\tsInit esInit -> go queue model tsInit esInit)
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
      nextT tree ts es (\tree' ts' es' -> go q' tree' ts' es')


extract :: Free f a -> a
extract (Pure a) = a

solve :: forall solver q a sig ts es. 
  (Solver solver, Queue q, Elem q~ (ts, Free (NonDet :+: sig) a, Label solver), Functor sig) =>
  q -> Free (CPSolve solver :+: NonDet :+: sig) a ->
    solver (Free (TransformerE ts es (Free (CPSolve solver :+: NonDet :+: sig) a) :+: sig) [a])
solve queue model = pure (initT @ts @es @sig (\ts es -> pure (ts, es))) >>= (\tses -> 
  let (ts, es) = extract tses in go queue model ts es)
  where 
    go :: q -> Free (CPSolve solver :+: NonDet :+: sig) a -> ts -> es ->
      solver (Free (TransformerE ts es (Free (CPSolve solver :+: NonDet :+: sig) a) :+: sig) [a])
    go q (Pure a) _ es = ((a:) <$>) <$> (continue q es)
    go q (NewVar k) ts es = do 
      v <- newvar 
      go q (k v) ts es
    go q (Dynamic d) ts es = d >>= (\t -> go q t ts es)
    go q (Add c k) ts es = do 
      successful <- addCons c 
      if successful then go q k ts es else go q fail ts es 
    go q (Fail) _ es = continue q es 
    go q (l :|: r) ts es = do 
      now <- mark 
      undefined
    continue :: q -> es -> solver (Free (TransformerE ts es (Free (CPSolve solver :+: NonDet :+: sig) a) :+: sig) [a])
    continue = undefined


it :: (Functor sig) => Free (TransformerE () () (Free (NonDet :+: Void) a) :+: sig) [a] -> Free Void [a] 
it (InitT k)    = it $ k () ()
it (LeftT _ k)  = it $ k ()
it (RightT _ k) = it (k ())
it (NextT x _ _ k) = it $ k x () ()
it (Pure a) = pure a

type CTransformer ts es = forall a tsRest esRest. 
  Free (TransformerE (ts, tsRest) (es, esRest) (Free (NonDet :+: Void) a) :+: Void) [a] ->
    Free (TransformerE tsRest esRest (Free (NonDet :+: Void) a) :+: Void) [a]

dbs_comp :: Int -> CTransformer Int ()
dbs_comp depthLimit = go 
  where 
    go :: CTransformer Int ()
    go (InitT k) = initT (\tsRest esRest -> go $ k (0, tsRest) ((), esRest))
    go (LeftT  (depth, tsRest) k) = leftT  tsRest (\tsRest' -> go $ k (depth+1, tsRest'))
    go (RightT (depth, tsRest) k) = rightT tsRest (\tsRest' -> go $ k (depth+1, tsRest'))
    go (NextT tree (depth, tsRest) (_, esRest) k) = nextT tree tsRest esRest (\tree' tsRest' esRest' -> 
      if depth <= depthLimit then go $ k tree' (depth, tsRest') ((), esRest') else go $ k fail (depth, tsRest') ((), esRest'))
    go (Pure a) = pure a

nbs_comp :: Int -> CTransformer () Int
nbs_comp node_limit = go 
  where 
    go :: CTransformer () Int
    go (InitT k) = initT (\tsRest esRest -> go $ k ((), tsRest) (0, esRest))
    go (LeftT  (_, tsRest) k) = leftT  tsRest (\tsRest' -> go $ k ((), tsRest'))
    go (RightT (_, tsRest) k) = rightT tsRest (\tsRest' -> go $ k ((), tsRest'))
    go (NextT tree (_, tsRest) (nodes, esRest) k) = nextT tree tsRest esRest (\tree' tsRest' esRest' -> 
      if nodes <= node_limit then go $ k tree' ((), tsRest') (nodes+1, esRest') else go $ k fail ((), tsRest') (nodes+1, esRest'))
    go (Pure a) = pure a 
    

test_dbs :: Solver solver => Int -> Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
test_dbs depthOuter depthInner model = run $ runEffects . it . (dbs_comp depthOuter) . (dbs_comp depthInner) .
  (traverseQ []) <$> eval model

test_nbs :: Solver solver => Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
test_nbs nodes model = run $ runEffects . it . (nbs_comp nodes) . (traverseQ []) <$> eval model

sols :: Solver solver => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
sols model = run $ runEffects . it . (traverseQ []) <$> eval model



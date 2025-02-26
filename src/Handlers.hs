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
import Effects (Sub (..), (:+:) (..), Void, runEffects)
import Control.Monad.Free (Free (..))
import Prelude hiding (fail)
import Solver (Solver (..))
import CPSolve (CPSolve, pattern NewVar, pattern Add, pattern Dynamic)
import Queues (Queue (..))
import Transformer (TransformerE, leftT, rightT, nextT, initT, pattern LeftT, pattern RightT, pattern NextT, pattern InitT, solT, pattern SolT)
import Data.Sequence (Seq)


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
  -- go q (Pure a) _ es    = (a:) <$> continue q es
  go q (Pure a) _ es = solT es (\es' -> (a:) <$> continue q es')
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
  (Solver solver, Queue q, Elem q~ (ts, Free (CPSolve solver :+: NonDet :+: sig) a, Label solver), Functor sig) =>
  q -> Free (CPSolve solver :+: NonDet :+: sig) a ->
    solver (Free (TransformerE ts es (Free (CPSolve solver :+: NonDet :+: sig) a) :+: sig) [a])
solve queue model = undefined 


it :: forall el a sig. (Functor sig) => Free (TransformerE () () el :+: sig) [a] -> Free Void [a] 
it (SolT _ k)   = it $ k ()
it (InitT k)    = it $ k () ()
it (LeftT _ k)  = it $ k ()
it (RightT _ k) = it (k ())
it (NextT x _ _ k) = it $ k x () ()
it (Pure a) = pure a

type CTransformer ts es = forall a tsRest esRest. 
  Free (TransformerE (ts, tsRest) (es, esRest) (Free (NonDet :+: Void) a) :+: Void) [a] ->
    Free (TransformerE tsRest esRest (Free (NonDet :+: Void) a) :+: Void) [a]

makeT :: forall ts es a tsRest esRest. ts -> es -> (es -> es) -> (ts -> ts) -> (ts -> ts) ->
  (ts -> es -> Free (NonDet :+: Void) a -> (ts, es, Free (NonDet :+: Void) a)) ->
    (Free (TransformerE (ts, tsRest) (es, esRest) (Free (NonDet :+: Void) a) :+: Void) [a] ->
      Free (TransformerE tsRest esRest (Free (NonDet :+: Void) a) :+: Void) [a])
makeT tsInit esInit solEs leftTs rightTs nextState = go 
  where 
    go :: Free (TransformerE (ts, tsRest) (es, esRest) (Free (NonDet :+: Void) a) :+: Void) [a] ->
      Free (TransformerE tsRest esRest (Free (NonDet :+: Void) a) :+: Void) [a]
    go (InitT k) = initT (\tsRest esRest -> go $ k (tsInit, tsRest) (esInit, esRest))
    go (SolT (es, esRest) k)  = solT esRest (\esRest' -> go $ k (solEs es, esRest'))
    go (LeftT  (ts, tsRest) k) = leftT  tsRest (\tsRest' -> go $ k (leftTs  ts, tsRest'))
    go (RightT (ts, tsRest) k) = rightT tsRest (\tsRest' -> go $ k (rightTs ts, tsRest'))
    go (NextT tree (ts, tsRest) (es, esRest) k) = let (ts', es', tree') = nextState ts es tree in 
      nextT tree' tsRest esRest (\tree'' tsRest' esRest' -> go $ k tree'' (ts', tsRest') (es', esRest'))
    go (Pure a) = pure a

fsC :: CTransformer () Bool
fsC = makeT () True (const False) id id 
  (\_ keepGoing tree -> if keepGoing then ((), keepGoing, tree) else ((), keepGoing, fail))

dbsC :: Int -> CTransformer Int () 
dbsC depthLimit = makeT 0 () id succ succ (\depth _ tree -> (depth, (), if depth <= depthLimit then tree else fail))

nbsC :: Int -> CTransformer () Int 
nbsC nodeLimit = makeT () 0 id id id (\_ nodes tree -> ((), nodes + 1, if nodes <= nodeLimit then tree else fail))

testDbs :: Solver solver => Int  -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testDbs  depth model = run $ runEffects . it . (dbsC depth) . (traverseQ []) <$> eval model


testNbs :: Solver solver => Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testNbs nodes model = run $ runEffects . it . (nbsC nodes) . (traverseQ []) <$> eval model

testNbs' :: Solver solver => Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testNbs' nodes model = run $ runEffects . it . (nbsC nodes) . (traverseQ []) <$> eval model

testDbsBfs :: Solver solver => Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testDbsBfs nodes model = run $ runEffects . it . (dbsC nodes) . (traverseQ (emptyQ :: Seq a)) <$> eval model


-- sols :: (Solver solver, Functor sig) => Free (CPSolve solver :+: (NonDet :+: sig)) a -> [a]
-- sols model = run $ runEffects . it <$> (solve [] model)



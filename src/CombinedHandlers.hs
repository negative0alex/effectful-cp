{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module CombinedHandlers (testNbsAfterDbs, nbsAfterDbsTraverseQ, testDbsTraverse, testNbsAfterDbsTraverse, testDbsNotReallyCPS, testDbsSlightlyCPS) where

import CPSolve
import Control.Monad.Free
import Effects
import Handlers
import NonDet
import Queues
import Solver
import Transformer
import Prelude hiding (fail)

-- should have the same semantics as `it . dbs`
dbsOnly ::
  forall sig a.
  (Functor sig) =>
  Int ->
  Free (TransformerE Int () (Free (NonDet :+: sig) a) :+: sig) [a] ->
  Free sig [a]
dbsOnly depthLimit = go
  where
    go :: Free (TransformerE Int () (Free (NonDet :+: sig) a) :+: sig) [a] -> Free sig [a]
    go (InitT k) = go $ k 0 ()
    go (SolT _u k) = go $ k ()
    go (LeftT depth k) = go $ k $ succ depth
    go (RightT depth k) = go $ k $ succ depth
    go (NextT tree depth u k) =
      let (ts', u', tree') = (id depth, id u, if depth <= depthLimit then tree else fail)
       in go $ k tree' ts' u'
    go (Pure a) = pure a
    go (Other op) = wrap (go <$> op)

-- should have the same semantics as `it . nbs . dbs`
nbsAfterDbs ::
  forall sig a.
  (Functor sig) =>
  Int ->
  Int ->
  Free (TransformerE (Int, ()) ((), Int) (Free (NonDet :+: sig) a) :+: sig) [a] ->
  Free sig [a]
nbsAfterDbs nodeLimit depthLimit = go
  where
    go :: Free (TransformerE (Int, ()) ((), Int) (Free (NonDet :+: sig) a) :+: sig) [a] -> Free sig [a]
    go (InitT k) = go $ k (0, ()) ((), 0)
    go (SolT ((), nodes) k) = go $ k $ (id (), id nodes)
    go (LeftT (depth, u) k) = go $ k $ (succ depth, id u)
    go (RightT (depth, u) k) = go $ k $ (succ depth, id u)
    go (NextT tree (depth, u1) (u2, nodes) k) =
      let (depth', u2', tree') =
            (id depth, id u2, if depth <= depthLimit then tree else fail)
          (u1', nodes', tree'') =
            ( id u1,
              succ nodes,
              if nodes <= nodeLimit then tree' else fail
            )
       in go $ k tree'' (depth', u1') (u2', nodes')
    go (Pure a) = pure a
    go (Other op) = wrap (go <$> op)

testNbsAfterDbs :: (Solver solver) => Int -> Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testNbsAfterDbs nodes depth model = run $ runEffects . (nbsAfterDbs nodes depth) . (traverseQ []) <$> eval model

-- combine dbs and traverseQ
dbsTraverseQ ::
  forall sig a q.
  (Queue q, Elem q ~ (Int, Free (NonDet :+: sig) a), Functor sig) =>
  Int ->
  q ->
  Free (NonDet :+: sig) a ->
  Free sig [a]
dbsTraverseQ depthLimit queue model = go queue model 0 () -- init happens immediately
  where
    go ::
      q ->
      Free (NonDet :+: sig) a ->
      Int ->
      () ->
      Free sig [a]
    go q (Pure a) _depth u = (a :) <$> continue q (id u) -- apply SolT transformation here
    go q (l :|: r) depth u = continue (pushQ (succ depth, l) $ pushQ (succ depth, r) q) u
    go q Fail _depth u = continue q u

    continue :: q -> () -> Free sig [a]
    continue q u
      | nullQ q = pure []
      | otherwise = do
          let ((depth, tree), q') = popQ q
          let (depth', u', tree') = (depth, u, if depth <= depthLimit then tree else fail)
          go q' tree' depth' u'

nbsAfterDbsTraverseQ ::
  forall sig a q.
  (Queue q, Elem q ~ ((Int, ()), Free (NonDet :+: sig) a), Functor sig) =>
  Int ->
  Int ->
  q ->
  Free (NonDet :+: sig) a ->
  Free sig [a]
nbsAfterDbsTraverseQ nodeLimit depthLimit queue model = go queue model (0, ()) ((), 0)
  where
    go ::
      q ->
      Free (NonDet :+: sig) a ->
      (Int, ()) ->
      ((), Int) ->
      Free sig [a]
    go q (Pure a) (_depth, u1) (_u2, nodes) = (a :) <$> continue q (id u1, id nodes)
    go q (l :|: r) (depth, u1) (u2, nodes) =
      continue (pushQ ((succ depth, id u1), l) $ pushQ ((succ depth, id u1), r) q) (u2, nodes)
    go q Fail _ts es = continue q es

    continue :: q -> ((), Int) -> Free sig [a]
    continue q (u1, nodes)
      | nullQ q = pure []
      | otherwise = do
          let (((depth, u2), tree), q') = popQ q
              (depth', u2', tree') = (depth, u2, if depth <= depthLimit then tree else fail)
              (u1', nodes', tree'') = (u1, succ nodes, if nodes <= nodeLimit then tree' else fail)
          go q' tree'' (depth', u1') (u2', nodes')

testDbsTraverse :: (Solver solver) => Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testDbsTraverse depth model = run $ runEffects . (dbsTraverseQ depth []) <$> eval model

testNbsAfterDbsTraverse :: (Solver solver) => Int -> Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testNbsAfterDbsTraverse nodes depth model = run $ runEffects . (nbsAfterDbsTraverseQ nodes depth []) <$> eval model

dbsNotReallyCPS ::
  forall sig a q.
  (Queue q, Elem q ~ (Int, Free (NonDet :+: sig) a), Functor sig) =>
  Int ->
  q ->
  Free (NonDet :+: sig) a ->
  Free sig [a]
dbsNotReallyCPS depthLimit queue model = go queue model 0 () id -- init happens immediately
  where
    go ::
      q ->
      Free (NonDet :+: sig) a ->
      Int ->
      () ->
      (Free sig [a] -> b) ->
      b
    go q (Pure a) _depth u cont = continue q u (\sol -> cont $ (a :) <$> sol) -- apply SolT transformation here
    go q (l :|: r) depth u cont = continue (pushQ (succ depth, l) $ pushQ (succ depth, r) q) u (\sol -> cont sol)
    go q Fail _depth u cont = continue q u cont

    continue :: q -> () -> (Free sig [a] -> b) -> b
    continue q u cont
      | nullQ q = cont . pure $ []
      | otherwise = do
          let ((depth, tree), q') = popQ q
          let (depth', u', tree') = (depth, u, if depth <= depthLimit then tree else fail)
          go q' tree' depth' u' cont

testDbsNotReallyCPS :: (Solver solver) => Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testDbsNotReallyCPS depth model = run $ runEffects . (dbsNotReallyCPS depth []) <$> eval model

idCPS :: a -> (a -> b) -> b
idCPS a cont = cont a

succCPS :: Int -> (Int -> b) -> b
succCPS i cont = cont (succ i)

dbsNextCont :: (Functor sig) => Int -> Int -> () -> Free (NonDet :+: sig) a -> ((Int, (), Free (NonDet :+: sig) a) -> b) -> b
dbsNextCont depthLimit depth u tree cont = cont (depth, u, if depth <= depthLimit then tree else fail)

dbsSlightlyCPS ::
  forall sig a q.
  (Queue q, Elem q ~ (Int, Free (NonDet :+: sig) a), Functor sig) =>
  Int ->
  q ->
  Free (NonDet :+: sig) a ->
  Free sig [a]
dbsSlightlyCPS depthLimit queue model = go queue model 0 () id -- init happens immediately
  where
    go ::
      q ->
      Free (NonDet :+: sig) a ->
      Int ->
      () ->
      (Free sig [a] -> b) ->
      b
    -- go q (Pure a) _depth u cont = continue q u (\sol -> cont $ (a :) <$> sol) -- apply SolT transformation here
    go q (Pure a) _depth u cont = idCPS u (\u' -> continue q u' (\sol -> cont $ (a:) <$> sol)) -- apply SolT transformation here
    go q (l :|: r) depth u cont = succCPS depth 
      (\depthL -> succCPS depth 
        (\depthR -> continue (pushQ (depthL, l) $ pushQ (depthR, r) q) u) cont)
    go q Fail _depth u cont = continue q u cont

    next = dbsNextCont @sig depthLimit

    continue :: q -> () -> (Free sig [a] -> b) -> b
    continue q u cont
      | nullQ q = cont $ pure []
      | otherwise =
          let ((depth, tree), q') = popQ q
           in next depth u tree (\(depth', u', tree') -> go q' tree' depth' u' cont)

testDbsSlightlyCPS :: (Solver solver) => Int -> Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testDbsSlightlyCPS depth model = run $ runEffects . (dbsSlightlyCPS depth []) <$> eval model


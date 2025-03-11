{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module CombinedHandlers where
import Control.Monad.Free
import NonDet
import Effects
import Transformer
import Prelude hiding (fail)

-- makeT ::
--   forall ts es a tsRest esRest sig.
--   (Functor sig) =>
--   ts ->
--   es ->
--   (es -> es) ->
--   (ts -> ts) ->
--   (ts -> ts) ->
--   (ts -> es -> Free (NonDet :+: sig) a -> (ts, es, Free (NonDet :+: sig) a)) ->
--   ( Free (TransformerE (ts, tsRest) (es, esRest) (Free (NonDet :+: sig) a) :+: sig) [a] ->
--     Free (TransformerE tsRest esRest (Free (NonDet :+: sig) a) :+: sig) [a]
--   )
-- makeT tsInit esInit solEs leftTs rightTs nextState = go
--   where
--     go ::
--       Free (TransformerE (ts, tsRest) (es, esRest) (Free (NonDet :+: sig) a) :+: sig) [a] ->
--       Free (TransformerE tsRest esRest (Free (NonDet :+: sig) a) :+: sig) [a]
--     go (InitT k) = initT (\tsRest esRest -> go $ k (tsInit, tsRest) (esInit, esRest))
--     go (SolT (es, esRest) k) = solT esRest (\esRest' -> go $ k (solEs es, esRest'))
--     go (LeftT (ts, tsRest) k) = leftT tsRest (\tsRest' -> go $ k (leftTs ts, tsRest'))
--     go (RightT (ts, tsRest) k) = rightT tsRest (\tsRest' -> go $ k (rightTs ts, tsRest'))
--     go (NextT tree (ts, tsRest) (es, esRest) k) =
--       let (ts', es', tree') = nextState ts es tree
--        in nextT tree' tsRest esRest (\tree'' tsRest' esRest' -> go $ k tree'' (ts', tsRest') (es', esRest'))
--     go (Pure a) = pure a
--     go (Other op) = wrap $ Inr (go <$> op)

-- dbsC :: Int -> CTransformer Int ()
-- dbsC depthLimit = makeT 0 () id succ succ (\depth _ tree -> (depth, (), if depth <= depthLimit then tree else fail))

-- nbsC :: Int -> CTransformer () Int
-- nbsC nodeLimit = makeT () 0 id id id (\_ nodes tree -> ((), nodes + 1, if nodes <= nodeLimit then tree else fail))

-- type CTransformer ts es =
--   forall a tsRest esRest sig. (Functor sig) =>
--   Free (TransformerE (ts, tsRest) (es, esRest) (Free (NonDet :+: sig) a) :+: sig) [a] ->
--   Free (TransformerE tsRest esRest (Free (NonDet :+: sig) a) :+: sig) [a]

-- should have the same semantics as `it . dbs`
dbsOnly :: forall sig a. (Functor sig) =>
  Int -> Free (TransformerE Int () (Free (NonDet :+: sig) a) :+: sig) [a] -> Free sig [a]
dbsOnly depthLimit = go 
  where 
    go :: Free (TransformerE Int () (Free (NonDet :+: sig) a) :+: sig) [a] -> Free sig [a]
    go (InitT k) = go $ k 0 ()
    go (SolT _u k) = go $ k ()
    go (LeftT depth k) = go $ k $ succ depth
    go (RightT depth k) = go $ k $ succ depth
    go (NextT tree depth u k) = let (ts', u', tree') = (id depth, id u, if depth <= depthLimit then tree else fail)
                                  in go $ k tree' ts' u'
    go (Pure a) = pure a 
    go (Other op) = wrap (go <$> op)

-- should have the same semantics as `it . nbs . dbs`
nbsAfterDbs :: forall sig a. (Functor sig) => 
  Int -> Int -> Free (TransformerE (Int, ()) ((), Int) (Free (NonDet :+: sig) a) :+: sig) [a] -> Free sig [a]
nbsAfterDbs nodeLimit depthLimit = go 
  where 
    go :: Free (TransformerE (Int, ()) ((), Int) (Free (NonDet :+: sig) a) :+: sig) [a] -> Free sig [a]
    go (InitT k) = go $ k (0, ()) ((), 0)
    go (SolT ((), nodes) k)  = go $ k $ (id (), id nodes)
    go (LeftT (depth, u) k)  = go $ k $ (succ depth, id u)
    go (RightT (depth, u) k) = go $ k $ (succ depth, id u)
    go (NextT tree (depth, u1) (u2, nodes) k) = let (depth', u2', tree') = 
                                                      (id depth, id u2, if depth <= depthLimit then tree else fail)
                                                    (u1', nodes', tree'') = (id u1, succ nodes,
                                                      if nodes <= nodeLimit then tree' else fail)
                                                in go $ k tree'' (depth', u1') (u2', nodes')
    go (Pure a) = pure a
    go (Other op) = wrap (go <$> op)
    
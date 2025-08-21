{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- {-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Transformers where

import Control.Monad.Free (Free, MonadFree (wrap))
import Effects.Algebra
import Effects.Core ((:+:) (..))
import Effects.NonDet (fail)
import Effects.Solver (SolverE)
import Effects.Transformer (TransformerE (..), initT, leftT, nextT, rightT, solT)
import Eval
import Handlers (flipT)
import Solver (Solver (..))
import System.Random
import Prelude hiding (fail)

type Transformer ts es solver a =
  forall ts' es'.
  TransformerTree (ts, ts') (es, es') solver a [a] ->
  TransformerTree ts' es' solver a [a]

makeT ::
  forall ts es solver a.
  (Solver solver) =>
  ts ->
  es ->
  (es -> es) ->
  (ts -> ts) ->
  (ts -> ts) ->
  (ts -> es -> SearchTree solver a -> (ts, es, SearchTree solver a)) ->
  Transformer ts es solver a
makeT tsInit esInit solEs leftTs rightTs nextState = handle (alg <| wrap . Inr) pure
 where
  alg ::
    TransformerE
      (ts, ts')
      (es, es')
      (SearchTree solver a)
      (TransformerTree ts' es' solver a [a]) ->
    TransformerTree ts' es' solver a [a]
  alg (InitT' k) = initT $ \tsRest esRest -> k (tsInit, tsRest) (esInit, esRest)
  alg (LeftT' (ts, tsRest) k) = leftT tsRest $ \tsRest' -> k (leftTs ts, tsRest')
  alg (RightT' (ts, tsRest) k) = rightT tsRest $ \tsRest' -> k (rightTs ts, tsRest')
  alg (SolT' (es, esRest) k) = solT esRest $ \esRest' -> k (solEs es, esRest')
  alg (NextT' tree (ts, tsRest) (es, esRest) k) =
    let (ts', es', tree') = nextState ts es tree
     in nextT tree' tsRest esRest $ \tree'' tsRest' esRest' -> k tree'' (ts', tsRest') (es', esRest')

makeTEff ::
  forall ts es ts' es' solver a.
  (Solver solver) =>
  ts ->
  es ->
  (es -> TransformerTree ts' es' solver a es) ->
  (ts -> TransformerTree ts' es' solver a ts) ->
  (ts -> TransformerTree ts' es' solver a ts) ->
  (ts -> es -> SearchTree solver a -> (ts, es, SearchTree solver a)) ->
  TransformerTree (ts, ts') (es, es') solver a [a] ->
  TransformerTree ts' es' solver a [a]
makeTEff tsInit esInit solEs leftTs rightTs nextState = handle (alg <| wrap . Inr) pure
 where
  alg ::
    TransformerE
      (ts, ts')
      (es, es')
      (SearchTree solver a)
      (TransformerTree ts' es' solver a [a]) ->
    TransformerTree ts' es' solver a [a]
  alg (InitT' k) = initT $ \tsRest esRest -> k (tsInit, tsRest) (esInit, esRest)
  alg (LeftT' (ts, tsRest) k) = leftT tsRest $ \tsRest' -> leftTs ts >>= \ts' -> k (ts', tsRest')
  alg (RightT' (ts, tsRest) k) = rightT tsRest $ \tsRest' -> rightTs ts >>= \ts' -> k (ts', tsRest')
  alg (SolT' (es, esRest) k) = solT esRest $ \esRest' -> solEs es >>= \es' -> k (es', esRest')
  alg (NextT' tree (ts, tsRest) (es, esRest) k) =
    let (ts', es', tree') = nextState ts es tree
     in nextT tree' tsRest esRest $ \tree'' tsRest' esRest' -> k tree'' (ts', tsRest') (es', esRest')

dbs :: (Solver solver) => Int -> Transformer Int () solver a
dbs depthLimit = makeT 0 () id succ succ $ \depth u tree -> (depth, u, if depth <= depthLimit then tree else fail)

nbs :: (Solver solver) => Int -> Transformer () Int solver a
nbs nodeLimit = makeT () 0 id id id $ \u nodes tree -> (u, nodes + 1, if nodes <= nodeLimit then tree else fail)

rand :: (Solver solver) => Int -> Transformer () [Bool] solver a
rand seed = makeT
  ()
  (randoms $ mkStdGen seed)
  id
  id
  id
  $ \u coins tree -> (u, tail coins, if head coins then flipT tree else tree)

lds :: (Solver solver) => Int -> Transformer Int () solver a
lds discrepancyLimit = makeT 0 () id id succ $ \disc u tree -> (disc, u, if disc <= discrepancyLimit then tree else fail)

it :: forall solver a. (Solver solver) => TransformerTree () () solver a [a] -> Free (SolverE solver) [a]
it = handle (alg <| wrap) pure
 where
  alg ::
    TransformerE () () (SearchTree solver a) (Free (SolverE solver) [a]) ->
    Free (SolverE solver) [a]
  alg (InitT' k) = k () ()
  alg (LeftT' _ k) = k ()
  alg (RightT' _ k) = k ()
  alg (SolT' _ k) = k ()
  alg (NextT' tree _ _ k) = k tree () ()


{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Staging.Effectful where

import Control.Monad.Free
import Effects.CPSolve
import Effects.Core
import Effects.NonDet
import Effects.Solver
import Effects.Transformer
import FD.OvertonFD
import Language.Haskell.TH
import Queens ((/\))
import Queues
import Solver (Solver (..))
import Staging.Handlers (rec2)
import Prelude hiding (fail)

-- import BranchAndBound

codeCurry :: (Rep a -> Rep b) -> Rep (a -> b)
codeCurry f = [||\a -> $$(f [||a||])||]

type Rep a = CodeQ a

type SearchTree solver a = Free (CPSolve solver :+: NonDet :+: SolverE solver) a

newtype StateTransform state solver = ST (Rep state -> Rep (Free (SolverE solver) state))

unST :: StateTransform state solver -> Rep state -> Rep (Free (SolverE solver) state)
unST (ST f) = f

newtype NextTransform ts es solver a
  = NT
      ( Rep ts ->
        Rep es ->
        Rep (SearchTree solver a) ->
        Rep (ts, es, SearchTree solver a)
      )

unNT :: NextTransform ts es solver a -> Rep ts -> Rep es -> Rep (SearchTree solver a) -> Rep (ts, es, SearchTree solver a)
unNT (NT f) = f

idState :: (Solver solver) => StateTransform state solver
idState = ST $ \s -> [||pure $$s||]

data (Solver solver) => SearchTransformer ts es solver a = SearchTransformer
  { tsInit :: Rep ts,
    esInit :: Rep es,
    leftTs :: StateTransform ts solver,
    rightTs :: StateTransform ts solver,
    solEs :: StateTransform es solver,
    nextState :: NextTransform ts es solver a
  }

dbsTrans :: (Solver solver) => Int -> SearchTransformer Int () solver a
dbsTrans depthLimit =
  SearchTransformer
    { tsInit = [||0||],
      esInit = [||()||],
      solEs = idState,
      leftTs = ST $ \ts -> [||pure $ $$ts + 1||],
      rightTs = ST $ \ts -> [||pure $ $$ts + 1||],
      nextState = NT $ \ts es model -> [||($$ts, $$es, if $$ts <= depthLimit then $$model else fail)||]
    }

-- branch and bound scaffolding

type Bound solver a = (SearchTree solver a) -> (SearchTree solver a)

type NewBound solver a = Rep (solver (Bound solver a))

data BBEvalState solver a = BBP Int (Bound solver a)

bbTrans ::
  forall a solver.
  (Solver solver) =>
  NewBound solver a ->
  SearchTransformer Int (BBEvalState solver a) solver a
bbTrans newBound =
  SearchTransformer
    { tsInit = [||0||],
      esInit = [||BBP 0 id||],
      solEs = ST $ \es ->
        [||let (BBP v _) = $$es in (solve $$newBound) >>= \b' -> pure $ BBP (v + 1) b'||],
      leftTs = idState,
      rightTs = idState,
      nextState = NT @Int @(BBEvalState solver a) @solver $ \ts es tree ->
        [||
        let (BBP nv bound) = $$es
            v = $$ts
         in if nv > v
              then do
                let tree' = bound (undefined)
                 in (nv, $$es, tree')
              else
                (v, $$es, $$tree)
        ||]
    }

newBound :: forall a. NewBound OvertonFD a
newBound =
  [||
  do
    obj <- fd_objective
    dom <- fd_domain $ obj
    let val = head dom
    return ((\tree -> obj @< val /\ tree))
  ||]

bb :: SearchTransformer Int (BBEvalState OvertonFD a) OvertonFD a
bb = bbTrans newBound

stage ::
  forall solver q ts es a.
  ( Solver solver,
    Queue q,
    Elem q ~ (Label solver, ts, SearchTree solver a)
  ) =>
  SearchTransformer ts es solver a ->
  Code
    Q
    (q -> SearchTree solver a -> Free (SolverE solver) [a])
stage (SearchTransformer tsInit esInit leftTs rightTs solEs nextState) =
  rec2
    ( \(go, continue) ->
        [||
        \ts es q tree -> case tree of
          Pure a -> do
            es' <- $$(unST solEs $ [||es||])
            (a :) <$> ($$continue es' q)
          l :|: r -> do
            now <- solve mark
            tsL <- $$(unST leftTs $ [||ts||])
            tsR <- $$(unST rightTs $ [||ts||])
            $$continue es (pushQ (now, tsL, l) $ pushQ (now, tsR, r) q)
          Fail -> $$continue es q
          (Add c k) -> do
            success <- solve @solver $ addCons c
            if success then $$go ts es q k else $$continue es q
          (NewVar k) -> do
            var <- solve @solver newvar
            $$go ts es q (k var)
          (Dynamic k) -> do
            term <- solve @solver k
            $$go ts es q term
          -- (Other op) -> Free . Inr $ (\t -> $$go ts es q t) <$> op
          (Solver k) -> solve' @solver $ ($$go ts es q) <$> k
        ||]
    )
    ( \(go, _) ->
        [||
        \es q ->
          if nullQ q
            then pure []
            else do
              let ((label, ts, tree), q') = popQ q
              let (ts', es', tree') = $$(unNT nextState [|| ts ||] [|| es ||] [|| tree ||])
              solve $ goto label
              $$go ts' es' q' tree'

                
        ||]
    )
    (\(go, _) -> [||$$go $$tsInit $$esInit||])
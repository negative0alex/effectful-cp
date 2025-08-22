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

module Staging.Direct where

import Control.Monad.Free
import Effects.CPSolve
import Effects.Core
import Effects.NonDet
import Effects.Solver
import FD.OvertonFD
import Transformers (flipT)
import Language.Haskell.TH
import Queens ((/\))
import Queues
import Solver (Solver (..))
import Staging.Old.Direct (rec2)
import System.Random
import Prelude hiding (fail)
import Eval (SearchTree)

showCode :: Code Q a -> IO ()
showCode code = do
  expr <- runQ (unTypeCode (code))
  putStrLn (pprint expr)

codeCurry :: (Rep a -> Rep b) -> Rep (a -> b)
codeCurry f = [||\a -> $$(f [||a||])||]

type Rep a = CodeQ a

newtype StateTransform state solver = ST {unST :: (Rep state -> Rep (Free (SolverE solver) state))}

newtype NextTransform ts es solver a
  = NT
  { unNT ::
      Rep ts ->
      Rep es ->
      Rep (SearchTree solver a) ->
      (Rep ts, Rep es, Rep (SearchTree solver a))
  }

idState :: (Solver solver) => StateTransform state solver
idState = ST $ \s -> [||pure $$s||]

data (Solver solver) => SearchTransformer ts es solver a = SearchTransformer
  { tsInit :: Rep ts
  , esInit :: Rep es
  , leftTs :: StateTransform ts solver
  , rightTs :: StateTransform ts solver
  , solEs :: StateTransform es solver
  , nextState :: NextTransform ts es solver a
  }

dbsTrans :: (Solver solver) => Int -> SearchTransformer Int () solver a
dbsTrans depthLimit =
  SearchTransformer
    { tsInit = [||0||]
    , esInit = [||()||]
    , solEs = idState
    , leftTs = ST $ \ts -> [||pure $ $$ts + 1||]
    , rightTs = ST $ \ts -> [||pure $ $$ts + 1||]
    , nextState = NT $ \ts es model -> (ts, es, [||if $$ts <= depthLimit then $$model else fail||])
    }

-- branch and bound scaffolding

type Bound solver a = (SearchTree solver a) -> (SearchTree solver a)

type NewBound solver a = Rep (solver (Bound solver a))

data BBEvalState solver a = BBP Int (Bound solver a)

bbNB ::
  forall a solver.
  (Solver solver) =>
  NewBound solver a ->
  SearchTransformer Int (BBEvalState solver a) solver a
bbNB newBound =
  SearchTransformer
    { tsInit = [||0||]
    , esInit = [||BBP 0 id||]
    , solEs = ST $ \es ->
        [||let (BBP v _) = $$es in (solve $$newBound) >>= \b' -> pure $ BBP (v + 1) b'||]
    , leftTs = idState
    , rightTs = idState
    , nextState = NT @Int @(BBEvalState solver a) @solver $ \ts es tree ->
        ( [||
          let (BBP nv _) = $$es
              v = $$ts
           in if nv > v then nv else v
          ||]
        , es
        , [||
          let (BBP nv bound) = $$es
              v = $$ts
           in if nv > v
                then bound ($$tree)
                else $$tree
          ||]
        )
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

bbS :: SearchTransformer Int (BBEvalState OvertonFD a) OvertonFD a
bbS = bbNB newBound

ldsS :: (Solver solver) => Int -> SearchTransformer Int () solver a
ldsS discLimit =
  SearchTransformer
    { tsInit = [||0||]
    , esInit = [||()||]
    , solEs = idState
    , leftTs = idState
    , rightTs = ST $ \disc -> [||pure $ $$disc + 1||]
    , nextState = NT $ \disc u tree ->
        ( disc
        , u
        , [||if $$disc <= discLimit then $$tree else fail||]
        )
    }

randS :: (Solver solver) => Int -> SearchTransformer () [Bool] solver a
randS seed =
  SearchTransformer
    { tsInit = [||()||]
    , esInit = [||randoms $ mkStdGen seed||]
    , solEs = idState
    , leftTs = idState
    , rightTs = idState
    , nextState = NT $ \u coins tree ->
        ( u
        , [||tail $$coins||]
        , [||let tree' = $$tree in if head $$coins then flipT tree' else tree'||]
        )
    }

stage ::
  forall solver q ts es a.
  ( Solver solver
  , Queue q
  , Elem q ~ (Label solver, ts, SearchTree solver a)
  ) =>
  SearchTransformer ts es solver a ->
  Code Q (q -> SearchTree solver a -> Free (SolverE solver) [a])
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
            success <- solve $ addCons c
            if success then $$go ts es q k else $$continue es q
          (NewVar k) -> do
            var <- solve newvar
            $$go ts es q (k var)
          (Dynamic k) -> do
            term <- solve k
            $$go ts es q term
          (Other2 op) -> Free $ (\t -> $$go ts es q t) <$> op
        ||]
    )
    ( \(go, _) ->
        [||
        \es q ->
          if nullQ q
            then pure []
            else
              let ((label, ts, tree), q') = popQ q
               in $$( let (ts', es', tree') = unNT nextState [||ts||] [||es||] [||tree||]
                       in [||$$go $$ts' $$es' q' ((solve $ goto label) >> $$tree')||]
                    )
        ||]
    )
    (\(go, _) -> [||$$go $$tsInit $$esInit||])

composeTrans ::
  (Solver solver) =>
  SearchTransformer ts1 es1 solver a ->
  SearchTransformer ts2 es2 solver a ->
  SearchTransformer (ts1, ts2) (es1, es2) solver a
composeTrans t1 t2 =
  SearchTransformer
    { tsInit = [||($$(tsInit t1), $$(tsInit t2))||]
    , esInit = [||($$(esInit t1), $$(esInit t2))||]
    , leftTs = ST $ \ts ->
        let ts1 = [||fst $$ts||]
            ts2 = [||snd $$ts||]
         in [||
            $$(unST (leftTs t1) $ ts1)
              >>= \ts1' ->
                $$(unST (leftTs t2) $ ts2)
                  >>= \ts2' -> pure (ts1', ts2')
            ||]
    , rightTs = ST $ \ts ->
        let ts1 = [||fst $$ts||]
            ts2 = [||snd $$ts||]
         in [||
            $$(unST (rightTs t1) $ ts1)
              >>= \ts1' ->
                $$(unST (rightTs t2) $ ts2)
                  >>= \ts2' -> pure (ts1', ts2')
            ||]
    , solEs = ST $ \es ->
        let es1 = [||fst $$es||]
            es2 = [||snd $$es||]
         in [||
            $$(unST (solEs t1) $ es1)
              >>= \es1' ->
                $$(unST (solEs t2) $ es2)
                  >>= \es2' -> pure (es1', es2')
            ||]
    , nextState = NT $ \ts es tree ->
        let ts1 = [||fst $$ts||]
            ts2 = [||snd $$ts||]
            es1 = [||fst $$es||]
            es2 = [||snd $$es||]
            (ts1', es1', tree') = unNT (nextState t1) ts1 es1 tree
            (ts2', es2', tree'') = unNT (nextState t2) ts2 es2 tree'
         in ([||($$ts1', $$ts2')||], [||($$es1', $$es2')||], tree'')
    }

(%&) ::
  (Solver solver) =>
  SearchTransformer ts1 es1 solver a ->
  SearchTransformer ts2 es2 solver a ->
  SearchTransformer (ts1, ts2) (es1, es2) solver a
(%&) = composeTrans
infixr 6 %&

---------------------------------------------------

bbLdsRandS :: Int -> Int -> SearchTransformer (((), (Int, Int))) (([Bool], ((), BBEvalState OvertonFD a))) OvertonFD a
bbLdsRandS seed discrepancy = (randS seed) %& (ldsS discrepancy) %& bbS

bbLdsRandCode ::
  Int -> Int -> Code
    Q
    ( [(Label OvertonFD, ((), (Int, Int)), SearchTree OvertonFD a)] ->
      SearchTree OvertonFD a ->
      Free (SolverE OvertonFD) [a]
    )
bbLdsRandCode seed discrepancy = stage (bbLdsRandS seed discrepancy)

justBBCode :: Code Q ([(Label OvertonFD, Int, SearchTree OvertonFD a)] -> SearchTree OvertonFD a -> Free (SolverE OvertonFD) [a])
justBBCode = stage bbS
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
import Effects.Algebra
import Effects.CPSolve
import Effects.NonDet
import Effects.Solver
import Eval (SearchTree)
import FD.OvertonFD
import Language.Haskell.TH
import Queens ((/\))
import Queues
import Solver (Solver (..))
import Staging.Old.Direct (rec2)
import System.Random
import Transformers (flipT)
import Prelude hiding (fail)

showCode :: Code Q a -> IO ()
showCode code = do
  expr <- runQ (unTypeCode (code))
  putStrLn (pprint expr)

type Rep a = CodeQ a

newtype StateTransform state solver = ST {unST :: (Rep state -> Rep (solver state))}

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
        [||let (BBP v _) = $$es in ($$newBound) >>= \b' -> pure $ BBP (v + 1) b'||]
    , leftTs = idState
    , rightTs = idState
    , nextState =
        NT @Int @(BBEvalState solver a) @solver $ \ts es tree ->
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
  Code Q (q -> SearchTree solver a -> solver [a])
stage (SearchTransformer tsInit esInit leftTs rightTs solEs nextState) =
  rec2
    ( \(go, continue) ->
        [||
        let
          -- algCSP :: CPSolve solver (ts -> es -> q -> solver [a]) -> ts -> es -> q -> solver [a]
          algCSP cps ts es q = case cps of
            (Add' c k) -> do
              success <- addCons c
              if success then k ts es q else $$continue es q
            (NewVar' k) -> do
              var <- newvar
              (k var) ts es q
            (Dynamic' d) -> do
              k <- d
              k ts es q
          -- algNonDet ::
          --   NonDet (SearchTree solver a, ts -> es -> q -> solver [a]) ->
          --   ts -> es -> q -> solver [a]
          algNonDet nd ts es q = case nd of
            (Try' (l, _) (r, _)) -> do
              now <- mark
              tsL <- $$(unST leftTs $ [||ts||])
              tsR <- $$(unST rightTs $ [||ts||])
              $$continue es (pushQ (now, tsL, l) $ pushQ (now, tsR, r) q)
            Fail' -> $$continue es q
          -- algSolver :: SolverE solver (ts -> es -> q -> solver [a]) -> ts -> es -> q -> solver [a]
          algSolver (RunSolver' s) ts es q = s >>= \k -> k ts es q
          -- genCSP :: a -> ts -> es -> q -> solver [a]
          genCSP a _ es q = do
            es' <- $$(unST solEs $ [||es||])
            (a :) <$> $$continue es' q
         in
          handlePara (liftPara algCSP <| algNonDet <| liftPara algSolver) genCSP
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
                       in [||$$go ((solve $ goto label) >> $$tree') $$ts' $$es' q'||]
                    )
        ||]
    )
    (\(go, _) -> [||\q model -> $$go model $$tsInit $$esInit q||])

stageOld ::
  forall solver q ts es a.
  ( Solver solver
  , Queue q
  , Elem q ~ (Label solver, ts, SearchTree solver a)
  ) =>
  SearchTransformer ts es solver a ->
  Code Q (q -> SearchTree solver a -> solver [a])
stageOld (SearchTransformer tsInit esInit leftTs rightTs solEs nextState) =
  rec2
    ( \(go, continue) ->
        [||
        \tree ts es q -> case tree of
          Pure a -> do
            es' <- $$(unST solEs $ [||es||])
            (a :) <$> ($$continue es' q)
          l :|: r -> do
            now <- mark
            tsL <- $$(unST leftTs $ [||ts||])
            tsR <- $$(unST rightTs $ [||ts||])
            $$continue es (pushQ (now, tsL, l) $ pushQ (now, tsR, r) q)
          Fail -> $$continue es q
          (Add c k) -> do
            success <- addCons c
            if success then $$go k ts es q else $$continue es q
          (NewVar k) -> do
            var <- newvar
            $$go (k var) ts es q
          (Dynamic k) -> do
            term <- k
            $$go term ts es q
          (Solver s) -> s >>= \term -> $$go term ts es q
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
                       in [||$$go ((solve $ goto label) >> $$tree') $$ts' $$es' q'||]
                    )
        ||]
    )
    (\(go, _) -> [||\q model -> $$go model $$tsInit $$esInit q||])

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
  Int ->
  Int ->
  Code
    Q
    ( [(Label OvertonFD, ((), (Int, Int)), SearchTree OvertonFD a)] ->
      SearchTree OvertonFD a ->
      OvertonFD [a]
    )
bbLdsRandCode seed discrepancy = stage (bbLdsRandS seed discrepancy)

bbLdsRandCodeOld ::
  Int ->
  Int ->
  Code
    Q
    ( [(Label OvertonFD, ((), (Int, Int)), SearchTree OvertonFD a)] ->
      SearchTree OvertonFD a ->
      OvertonFD [a]
    )
bbLdsRandCodeOld seed discrepancy = stageOld (bbLdsRandS seed discrepancy)

justBBCode :: Code Q ([(Label OvertonFD, Int, SearchTree OvertonFD a)] -> SearchTree OvertonFD a -> OvertonFD [a])
justBBCode = stage bbS
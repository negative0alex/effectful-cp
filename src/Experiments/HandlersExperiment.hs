{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE TransformListComp #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE StarIsType #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Experiments.HandlersExperiment where

import Effects.CPSolve (CPSolve, pattern Add, pattern Dynamic, pattern NewVar, dynamic, exist, in_domain, (@\=), (@\==), (@+), (@=))
import Control.Monad.Free (Free (..), MonadFree (wrap))
import Data.Sequence (Seq)
import Effects.Core (Sub (..), Void, unitr, wrapF, (:+:) (..), pattern Other)
import Effects.NonDet (NonDet (..), fail, pattern Fail, pattern (:|:), try)
import Queues (Queue (..))
import Solver (Solver (..))
import Effects.Transformer (TransformerE, initT, leftT, nextT, rightT, solT, pattern InitT, pattern LeftT, pattern NextT, pattern RightT, pattern SolT)
import Prelude hiding (fail)
import Handlers (it)
import FD.OvertonFD
import qualified FD.OvertonFD as OvertonFD
import qualified FD.Domain as Domain
import GHC.Exts (sortWith)
import Data.List
import Effects.Lift

-- put solver at the end
solve ::
  forall q a sig ts es.
  (Queue q, Elem q ~ (ts, Free (CPSolve OvertonFD :+: sig) a, Label OvertonFD), Functor sig,
  Solv OvertonFD `Sub` sig, NonDet `Sub` sig) =>
  q ->
  Free (CPSolve OvertonFD :+: sig) a ->
  Free (TransformerE ts es (Free (CPSolve OvertonFD :+: sig) a) :+: sig) [a]
solve queue model = initT (\tsInit esInit -> go tsInit esInit queue model)
  where
    go ::
      ts ->
      es ->
      q ->
      Free (CPSolve OvertonFD :+: sig) a ->
      Free (TransformerE ts es (Free (CPSolve OvertonFD :+: sig) a) :+: sig) [a]
    go _ es q (Pure a) = solT es (\es' -> (a :) <$> continue q es')
    go ts es q (l :|: r) = do
      Effects.Lift.mark $ \now ->
        leftT ts (\leftS -> rightT ts (\rightS -> continue (pushQ (leftS, l, now) $ pushQ (rightS, r, now) q) es))
    go _ es q Fail = continue q es
    go ts es q (NewVar k) = do 
      Effects.Lift.newvar @OvertonFD $ \v ->
        go ts es q (k v)
    go ts es q (Add c k) = do 
      Effects.Lift.addCons @OvertonFD c $ \successful ->
        if successful then go ts es q k else go ts es q fail
    go ts es q (Dynamic k) = do 
      Effects.Lift.runS  @OvertonFD k $ \term ->
        go ts es q term

    continue :: q -> es -> Free (TransformerE ts es (Free (CPSolve OvertonFD :+: sig) a) :+: sig) [a]
    continue q es
      | nullQ q = pure []
      | otherwise = do
          let ((ts,tree,label), q') = popQ q
          Effects.Lift.goto label $ \_ ->
            nextT tree ts es (\tree' ts' es' -> go ts' es' q' tree')

propagateConstraints :: forall solver a. (Solver solver) => Free (solver :+: Void) [a] -> solver [a]
propagateConstraints = go . unitr
  where
    go :: Free (solver) [a] -> solver [a]
    go (Pure as) = pure as
    go (Free solv) = solv >>= go

allDbs :: forall solver q a sig.
  (Solver solver, Queue q, Elem q ~ (Int, Free (CPSolve solver :+: NonDet :+: sig) a, Label solver), solver `Sub` sig) =>
  Int -> 
  q ->
  Free (CPSolve solver :+: NonDet :+: sig) a ->
  Free sig [a]
allDbs depthLimit queue model = go queue model 0 ()
  where 
    go ::
      q ->
      Free (CPSolve solver :+: NonDet :+: sig) a ->
      Int ->
      () ->
      Free sig [a]
    go q (Pure a) _depth u = (a :) <$> continue q (id u)
    go q (l :|: r) depth u = do 
      now <- wrapF Solver.mark 
      continue (pushQ (succ depth, l, now) $ pushQ (succ depth, r, now) q) u
    go q Fail _depth u = continue q u
    go q (NewVar k) depth u = do 
      v <- wrapF @solver Solver.newvar 
      go q (k v) depth u
    go q (Add c k) depth u = do 
      successful <- wrapF @solver (Solver.addCons c)
      if successful then go q k depth u else go q fail depth u
    go q (Dynamic k) depth u = do 
      term <- wrapF @solver k
      go q term depth u

    continue :: q -> () -> Free sig [a]
    continue q u
      | nullQ q = pure []
      | otherwise = do
          let ((depth, tree, label), q') = popQ q
          wrapF @solver (Solver.goto label)
          let (depth', u', tree') = (id depth, id u, if depth <= depthLimit then tree else fail)
          go q' tree' depth' u'

type CTransformer' ts es a tsRest esRest solver sig =
  (Functor sig, Solver solver, Solv solver `Sub` sig,
    CPSolve solver `Sub` sig, NonDet `Sub` sig) =>
  Free (TransformerE (ts, tsRest) (es, esRest) (Free sig a) :+: sig) [a] ->
  Free (TransformerE tsRest esRest (Free sig a) :+: sig) [a]

makeT' ::
  forall solver ts es a sig tsRest esRest.
  (Functor sig, Solver solver, Solv solver `Sub` sig, NonDet `Sub` sig, CPSolve solver `Sub` sig) =>
  ts ->
  es ->
  (es -> es) ->
  (ts -> ts) ->
  (ts -> ts) ->
  (ts -> es -> Free sig a -> (ts, es, Free sig a)) ->
  CTransformer' ts es a tsRest esRest solver sig
makeT' tsInit esInit solEs leftTs rightTs nextState = go
  where
    go :: Free (TransformerE (ts, tsRest) (es, esRest) (Free sig a) :+: sig) [a] ->
      Free (TransformerE tsRest esRest (Free sig a) :+: sig) [a]
    go (InitT k) = initT (\tsRest esRest -> go $ k (tsInit, tsRest) (esInit, esRest))
    go (SolT (es, esRest) k) = solT esRest (\esRest' -> go $ k (solEs es, esRest'))
    go (LeftT (ts, tsRest) k) = leftT tsRest (\tsRest' -> go $ k (leftTs ts, tsRest'))
    go (RightT (ts, tsRest) k) = rightT tsRest (\tsRest' -> go $ k (rightTs ts, tsRest'))
    go (NextT tree (ts, tsRest) (es, esRest) k) =
      let (ts', es', tree') = nextState ts es tree
       in nextT tree' tsRest esRest (\tree'' tsRest' esRest' -> go $ k tree'' (ts', tsRest') (es', esRest'))
    go (Pure a) = pure a
    go (Other op) = wrap $ Inr (go <$> op)


destroyNonDet :: (Functor sig) => Free (NonDet :+: sig) a -> Free sig a 
destroyNonDet (Pure a) = pure a 
destroyNonDet (Free f) = case f of 
  Inl _  -> undefined 
  Inr fr -> Free $ destroyNonDet <$> fr
dbs' depthLimit = makeT' 0 () id succ succ (\depth _ tree -> (depth, (), if depth <= depthLimit then tree else fail))

fs' :: forall a tsRest esRest solver sig. 
  (Functor sig, Solver solver, Solv solver `Sub` sig, NonDet `Sub` sig, CPSolve solver `Sub` sig) =>
  CTransformer' () Bool a tsRest esRest solver sig
fs' = makeT' @solver () True (const False) id id
    (\_ keepGoing tree -> ((), keepGoing, if keepGoing then tree else fail))

testSolver :: CSP a -> [a]
testSolver model = runSolver . destroyNonDet . it . (solve []) $ model

-- testSolverDbs depth model = run . propagateConstraints . it . (dbs' depth) . (solve (emptyQ :: Seq a)) $ model

-- testSolverFs model = run . propagateConstraints . it . fs' . (solve []) $ model

testAllDbs depth model = run . propagateConstraints . (allDbs depth []) $ model

-- -------| MODIFIED QUEENS

type CSP = Free (CPSolve OvertonFD :+: NonDet :+: Solv OvertonFD :+: Void)

nqueens :: Int -> CSP [Int]
nqueens n = exist @OvertonFD n $ \queens -> model queens n /\ enumerate queens /\ assignments queens

model :: [FDVar] -> Int -> CSP ()
model queens n = queens `allin` (1,n) /\ alldifferent queens /\ diagonals queens

allin :: [FDVar] -> (Int, Int) -> CSP ()
allin queens range = conj [q `in_domain` range | q <- queens]

alldifferent :: [FDVar] -> CSP ()
alldifferent queens = conj [qi @\= qj | qi : qjs <- tails queens, qj <- qjs]

diagonals :: [FDVar] -> CSP ()
diagonals queens = conj [ (qi @\== (qj @+ d)) /\ (qj @\== (qi @+ d)) | qi : qjs <- tails queens, (qj, d) <- zip qjs [1..]]
-- enumerate queens values = conj [ enum queen values | queen <- queens]

enum :: FDVar -> [Int] -> CSP ()
enum var values = disj [ var @= value | value <- values ]

disj :: [CSP ()] -> CSP ()
disj = foldl (\/) false

conj :: [CSP ()] -> CSP ()
conj = foldl (/\) true

(\/) :: CSP a -> CSP a -> CSP a
(\/) = try

false :: CSP a
false = fail

true :: CSP ()
true = pure ()

(/\) :: CSP a -> CSP b -> CSP b
(/\) = (>>)


-- -----------------------| Labelling |------------------------

enumerate :: [FDVar] -> CSP ()
enumerate vs = dynamic (label firstfail id vs)

label :: ([FDVar] -> OvertonFD [FDVar]) -> ([Int] -> [Int]) ->
  [FDVar] -> OvertonFD (CSP ())
label varsel valsel vs = do
  vs' <- varsel vs
  label' vs'
  where
    label' [] = pure . pure $ ()
    label' (v:vs) = do
      -- d <- valsel $ Domain.elems $ OvertonFD.lookup v
      d <- fd_domain v
      let d' = valsel d
      pure $ enum v d' /\ dynamic (label varsel valsel vs)

firstfail :: [FDVar] -> OvertonFD [FDVar]
firstfail vs = do
  ds <- mapM OvertonFD.lookup vs
  return [v | (d,v) <- zip ds vs, then sortWith by Domain.size d]

middleout :: [a] -> [a]
middleout l = let n = length l `div` 2 in
  interleave (drop n l) (reverse $ take n l)

interleave :: [a] -> [a] -> [a]
interleave [] ys = ys
interleave (x:xs) ys = x:interleave ys xs

-- ----------------------| Assignment |----------------------

assignments :: [FDVar] -> CSP [Int]
assignments = mapM assignment 
assignment :: Sub (CPSolve OvertonFD) sig => FDVar -> Free sig Int
assignment q = dynamic $ do 
  d <- fd_domain q
  let v = head d
  pure $ pure v


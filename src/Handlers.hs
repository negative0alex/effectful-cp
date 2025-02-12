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
import SplitCPEffects (Sub (..), (:+:) (..), pattern Other, Void, runEffects, inject, getRUnsafe)
import Control.Monad.Free (Free (..), hoistFree)
import Control.Monad (liftM2)
import Prelude hiding (fail)
import Solver (Solver (..))
import CPSolve (CPSolve, pattern NewVar, pattern Add, pattern Dynamic)
import Queues (QueueE, pop, push, Queue (..), pattern Push, pattern Pop)
import Data.Sequence (Seq)

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

solveNaive model = run $ runEffects . naiveAllSols <$> eval model
solveDFS model = run $ runEffects . traverseQueue [] . queueify <$> eval model
solveBFS model = run $ runEffects . traverseQueue (emptyQ :: Seq a) . queueify <$> eval model
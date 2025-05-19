{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Experiments.CombinedHandlers where

import Effects.CPSolve
import Control.Monad.Free
import Effects.Core
import Handlers
import Effects.NonDet
import Queues
import Solver
import Effects.Transformer
import Prelude hiding (fail)
import System.Random



exampleT :: forall sig a q.
  (Queue q, Elem q ~ (Int, Free (NonDet :+: sig) a), Functor sig) =>
  Int ->
  Int -> 
  Int ->
  q ->
  Free (NonDet :+: sig) a ->
  Free sig [a]
exampleT nodeLimit seed depthLimit = go 0 (randoms $ mkStdGen seed , 0) 
  where 
    go :: Int -> ([Bool], Int) -> q -> Free (NonDet :+: sig) a -> Free sig [a]
    go ts es q (Pure a) = (a:) <$> continue es q 
    go ts es q (l :|: r) = continue es $ pushQ (ts + 1, l) $ pushQ (ts + 1, r) q 
    go ts es q Fail = continue es q 

    continue :: ([Bool], Int) -> q -> Free sig [a]
    continue es q 
      | nullQ q = pure []
      | otherwise = 
        let ((depth, tree), q') = popQ q 
            (coins, nodes) = es 
            tree' = if head coins then flipT tree else tree
          in go depth (tail coins, nodes + 1) q' 
            (if depth <= depthLimit && nodes <= nodeLimit then tree' else fail)


exampleE :: forall a q solver. 
  (Solver solver, Queue q, Elem q ~ (Label solver, Int, Free (CPSolve solver :+: NonDet :+: Void) a) ) =>
  Int ->
  Int -> 
  Int ->
  q ->
  Free (CPSolve solver :+: NonDet :+: Void) a ->
  solver [a]
exampleE nodeLimit seed depthLimit = go 0 (randoms $ mkStdGen seed, 0)
  where 
    go ts es q (Pure a) = (a:) <$> continue es q 
    go ts es q (l :|: r) = do 
      now <- mark
      continue es $ pushQ (now, ts + 1, l) $ pushQ (now, ts + 1, r) q 
    go ts es q Fail = continue es q 
    go ts es q (NewVar k) = do 
      var <- newvar 
      go ts es q (k var)
    go ts es q (Add c k) = do 
      s <- addCons c 
      if s then go ts es q k else continue es q 
    go ts es q (Dynamic k) = do 
      t <- k 
      go ts es q t

    continue es q 
      | nullQ q = pure []
      | otherwise = do
        let ((now, depth, tree), q') = popQ q 
        let (coins, nodes) = es 
        let  tree' = if head coins then flipT tree else tree
        goto now
        go depth (tail coins, nodes + 1) q' 
            (if depth <= depthLimit && nodes <= nodeLimit then tree' else fail)

testExampleTraverse :: (Solver solver) => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testExampleTraverse model = run $ runEffects . (exampleT 18000 300 25 []) <$> eval model

testExampleEval :: (Solver solver) => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a] 
testExampleEval model = run $ (exampleE 18000 300 25 []) model
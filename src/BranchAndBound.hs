{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE ImpredicativeTypes #-}
module BranchAndBound where
import Control.Monad.Free (Free (..))
import Effects.CPSolve (CPSolve, (@<), exists, (@>), in_domain)
import Effects.Core (Void, runEffects, (:+:) (..), liftR)
import Effects.NonDet (NonDet (..), pattern (:|:))
import Effects.Transformer (TransformerE, pattern InitT, pattern LeftT, pattern NextT, pattern RightT, pattern SolT)
import Solver (Solver (..))
import Prelude hiding (fail)
import Handlers (eval, traverseQ)
import FD.OvertonFD (OvertonFD, fd_domain, fd_objective)
import Queens



type Bound solver = forall a. 
  Free (CPSolve solver :+: NonDet :+: Void) a ->
  Free (CPSolve solver :+: NonDet :+: Void) a
type NewBound solver = solver (Bound solver)

data BBEvalState solver = BBP Int (Bound solver)

bb :: forall a solver. (Solver solver) => NewBound solver -> 
  Free (TransformerE Int (BBEvalState solver) (Free (NonDet :+: Void) a) :+: Void) [a] ->
  solver (Free Void [a])
bb newBound = go 
  where 
    go :: Free (TransformerE Int (BBEvalState solver) (Free (NonDet :+: Void) a) :+: Void) [a] ->
      solver (Free Void [a])
    go (Pure a) = pure . pure $ a
    go (InitT k) = go $ k 0 (BBP 0 id)
    go (SolT (BBP v _) k) = do 
       bound' <- newBound 
       go $ k (BBP (v+1) bound')
    go (LeftT ts k) = go $ k ts
    go (RightT ts k) = go $ k ts
    go (NextT tree v es@(BBP nv bound) k) = if nv > v then
      do 
        tree' <- eval (bound $ liftR tree)
        go $ k tree' nv es
      else 
      go $ k tree v es

bbSolve :: Free (CPSolve OvertonFD :+: (NonDet :+: Void)) a -> [a]
bbSolve model = run $ runEffects <$> (((traverseQ []) <$> eval model) >>= (bb newBound))

bbSolve' :: Free (CPSolve OvertonFD :+: (NonDet :+: Void)) a -> [a]
bbSolve' model = run $ do 
  model' <- eval model 
  sols <- bb newBound (traverseQ [] model')
  return $ runEffects sols

newBound :: NewBound OvertonFD 
newBound = do 
  obj <- fd_objective
  dom <- fd_domain $ obj 
  let val = head dom
  return ((\tree -> obj @< val /\ tree) :: Bound OvertonFD)

gmodel :: Int -> CSP Int
gmodel n = exists @OvertonFD $ \_ -> path 1 n 0

path :: Int -> Int -> Int -> CSP Int
path x y d 
  | x == y = pure d 
  | otherwise = disj [undefined $ (fd_objective >>= \o -> 
                          pure (o @> (d+d'-1) /\ (path z y (d + d')))) | (z,d') <- edge x]

edge :: (Ord a, Num a, Num b) => a -> [(a, b)]
edge i | i < 20 = [(i+1, 4), (i+2, 1)]
       | otherwise = []

aaa :: CSP [Int]
aaa = exists @OvertonFD $ \a -> a @> 2 /\ a @< 5 /\ enumerate [a] /\ assignments [a]
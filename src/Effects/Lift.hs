{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Effects.Lift where

import Control.Monad.Free (Free(..))
import Effects.Core (Sub, project, inject, (:+:), pattern Other, Void)
import Solver

data Lift m k where 
  Lift' :: (Monad m) => m k -> Lift m k 

instance Functor (Lift m) where 
  fmap :: (a -> b) -> Lift m a -> Lift m b
  fmap f (Lift' ma) = Lift' (f <$> ma)

pattern LiftM :: (Lift m `Sub` sig, Monad m) => m (Free sig a) -> Free sig a 
pattern LiftM mk <- (project -> Just (Lift' mk))
liftM :: (Lift m `Sub` sig, Monad m) => m (Free sig a) -> Free sig a 
liftM mk = inject (Lift' mk)

data Solv solver k where 
  Newvar'  :: (Solver solver) => (Term solver -> k) -> Solv solver k 
  AddCons' :: (Solver solver) => Constraint solver -> (Bool -> k) -> Solv solver k
  Mark'    :: (Solver solver) => (Label solver -> k) -> Solv solver k 
  Goto'    :: (Solver solver) => Label solver -> (() -> k) -> Solv solver k
  RunS'     :: (Solver solver) => solver b -> (b -> k) -> Solv solver k

instance (Solver solver) => Functor (Solv solver) where 
  fmap :: Solver solver => (a -> b) -> Solv solver a -> Solv solver b
  fmap f (Newvar' cont) = Newvar' (f . cont)
  fmap f (AddCons' c cont) = AddCons' c (f . cont)
  fmap f (Mark' cont) = Mark' (f . cont)
  fmap f (Goto' label cont) = Goto' label (f . cont)
  fmap f (RunS' term cont) = RunS' term (f . cont)

pattern Newvar :: (Sub (Solv solver) sup, Solver solver) => Solver solver => (Term solver -> Free sup a) -> Free sup a
pattern Newvar cont <- (project -> Just (Newvar' cont))
newvar :: (Sub (Solv solver) sup, Solver solver) => (Term solver -> Free sup a) -> Free sup a
newvar cont = inject (Newvar' cont) 

pattern AddCons :: (Sub (Solv solver) sup, Solver solver) =>
  Solver solver => Constraint solver -> (Bool -> Free sup a) -> Free sup a
pattern AddCons c cont <- (project -> Just (AddCons' c cont))
addCons :: (Sub (Solv solver) sup, Solver solver) => Constraint solver -> (Bool -> Free sup a) -> Free sup a
addCons c cont = inject (AddCons' c cont)

pattern Mark :: (Sub (Solv solver) sup, Solver solver) => Solver solver => (Label solver -> Free sup a) -> Free sup a
pattern Mark cont <- (project -> Just (Mark' cont))
mark :: (Sub (Solv solver) sup, Solver solver) => (Label solver -> Free sup a) -> Free sup a
mark cont = inject (Mark' cont)

pattern Goto :: (Sub (Solv solver) sup, Solver solver) => Solver solver => Label solver -> (() -> Free sup a) -> Free sup a
pattern Goto label cont <- (project -> Just (Goto' label cont))
goto :: (Sub (Solv solver) sup, Solver solver) => Label solver -> (() -> Free sup a) -> Free sup a
goto label cont = inject (Goto' label cont)

pattern RunS :: (Sub (Solv solver) sup, Solver solver) => Solver solver => solver b -> (b -> Free sup a) -> Free sup a
pattern RunS term cont <- (project -> Just (RunS' term cont))
runS :: (Sub (Solv solver) sup, Solver solver) => solver b -> (b -> Free sup a) -> Free sup a
runS term cont = inject (RunS' term cont)

  
runSolver' :: (Solver solver) => Free (Solv solver :+: Void) a -> solver a
runSolver' (Pure a) = pure a
runSolver' (Newvar k) = do 
  v <- Solver.newvar 
  runSolver' $ k v
runSolver' (AddCons c k) = do 
  success <- Solver.addCons c 
  runSolver' $ k success
runSolver' (Mark k) = do 
  now <- Solver.mark 
  runSolver' $ k now 
runSolver' (Goto l k) = do 
  Solver.goto l 
  runSolver' $ k () 
runSolver' (RunS s k) = do 
  term <- s
  runSolver' $ k term 

runSolver :: (Solver solver) => Free (Solv solver :+: Void) a -> a
runSolver = Solver.run . runSolver'

data EvState es k where 
  Ev' :: (es -> (es,k)) -> EvState es k 

instance Functor (EvState es) where
  fmap :: (a -> b) -> EvState es a -> EvState es b
  fmap f (Ev' cont) = Ev' $ \es -> let (es', a) = cont es in (es', f a)

pattern Ev :: Sub (EvState es) sup => (es -> (es, Free sup a)) -> Free sup a
pattern Ev cont <- (project -> Just (Ev' cont)) 

ev :: Sub (EvState es) sup => (es -> (es, Free sup a)) -> Free sup a
ev cont = inject (Ev' cont)
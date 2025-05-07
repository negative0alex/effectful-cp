{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# LANGUAGE InstanceSigs #-}
module Effects.CPSolve (
  CPSolve(..)
, pattern Dynamic
, dynamic
, pattern NewVar
, newVar
, exists
, pattern Add
, add
, exist
, in_domain
, (@=)
, (@+)
, (@\=)
, (@\==)
, addSum) where
import Control.Monad.Free (Free (..))
import Effects.Core (Sub(..), project, inject)
import FD.OvertonFD (OvertonFD, OPlus ((:+)), OConstraint (..))
import Solver(Solver(..))

data CPSolve solver a where
  NewVar'  :: (Term solver -> a) -> CPSolve solver a
  Add'     :: (Constraint solver) -> a -> CPSolve solver a
  Dynamic' :: solver a -> CPSolve solver a
  deriving Functor

pattern Dynamic a <- (project -> (Just (Dynamic' a)))


dynamic :: (Functor solver, CPSolve solver `Sub` sig) => solver (Free sig a) -> Free sig a
dynamic = inject . Dynamic'

pattern NewVar :: forall solver sig a. (Solver solver, CPSolve solver `Sub` sig) => 
  (Term solver -> Free sig a) -> Free sig a

pattern NewVar k <- (project -> Just (NewVar' k))


newVar :: forall solver sig. (Solver solver, CPSolve solver `Sub` sig) =>
  Free sig (Term solver)
newVar = inject (NewVar' pure)

exists :: forall solver sig a. (Solver solver, CPSolve solver `Sub` sig) =>
  (Term solver -> Free sig a) -> Free sig a
exists = inject . NewVar'

pattern Add :: forall solver sup a.
  (Sub (CPSolve solver) sup, Functor solver) => Constraint solver -> Free sup a -> Free sup a
pattern Add c k <- (project -> Just (Add' c k))
add :: forall solver sig. (Solver solver, CPSolve solver `Sub` sig) =>
  Constraint solver -> Free sig ()
add c = inject (Add' c (pure ()))

-- --------------| Sugar |--------------

-- | Generates `n` new solver variables.
exist :: forall solver sig a. (Solver solver, CPSolve solver `Sub` sig) =>
  Int -> ([Term solver] -> Free sig a) -> Free sig a
exist n k = go n $ pure []
  where
    go :: Int -> Free sig [Term solver] -> Free sig a
    go 0 acc = acc >>= k
    go n' acc = do
      v <- newVar
      go (n' - 1) ((v :) <$> acc)

in_domain :: (CPSolve OvertonFD `Sub` sig) => Term OvertonFD -> (Int, Int) -> Free sig ()
v `in_domain` r = add (OInDom v r)

(@=) :: (CPSolve OvertonFD `Sub` sig) => Term OvertonFD -> Int -> Free sig ()
v @= n = add (OHasValue v n)

(@+) :: Term OvertonFD -> Int -> OPlus
(@+) = (:+)

(@\=) :: (CPSolve OvertonFD `Sub` sig) => Term OvertonFD -> Term OvertonFD -> Free sig ()
v1 @\= v2 = add (ODiff v1 v2)

(@\==) :: (CPSolve OvertonFD `Sub` sig) => Term OvertonFD -> OPlus -> Free sig ()
v1 @\== (v2 :+ n) = do
  n' <- newVar
  t2 <- newVar
  add (OHasValue n' n)
  add (OAdd t2 v2 n')
  add (ODiff t2 v1)

addSum :: (CPSolve OvertonFD `Sub` sig) => Term OvertonFD -> Term OvertonFD -> Term OvertonFD -> Free sig ()
addSum a b c = add @OvertonFD (OAdd a b c)
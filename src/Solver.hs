{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
module Solver (Solver(..)) where

class (Monad solver) => Solver solver where
  type Constraint solver = r | r -> solver
  type Term solver = r | r -> solver
  type Label solver = r | r -> solver

  newvar :: solver (Term solver)
  addCons :: Constraint solver -> solver Bool
  run :: solver a -> a
  mark :: solver (Label solver)
  goto :: Label solver -> solver ()



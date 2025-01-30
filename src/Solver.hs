{-# LANGUAGE TypeFamilyDependencies #-}
module Solver (Solver(..)) where
import Data.Kind (Type)


class (Monad solver) => Solver solver where
  type Constraint solver :: Type
  type Term solver :: Type
  type Label solver :: Type

  newvar :: solver (Term solver)
  addCons :: Constraint solver -> solver Bool
  run :: solver a -> a
  mark :: solver (Label solver)
  goto :: Label solver -> solver ()
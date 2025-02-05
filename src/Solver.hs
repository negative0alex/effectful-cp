{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
module Solver (Solver(..), SolverEffect(..)) where
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

class (Functor sig, Solver(Solv sig)) => SolverEffect sig where
  type Solv sig :: (Type -> Type)

  newVar'  :: (Term (Solv sig) -> a) -> sig a
  addCons' :: Constraint (Solv sig) -> a -> sig a
  dynamic' :: Solv sig a -> sig a


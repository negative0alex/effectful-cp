{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
module CPSolve where
import CPEffects (Solver(..))
import Control.Monad.Free (Free)
import SplitCPEffects (Sub, project, inject)

data CPSolve solver a where
  NewVar'  :: (Term solver -> a) -> CPSolve solver a
  Add'     :: (Constraint solver) -> a -> CPSolve solver a
  Dynamic' :: solver a -> CPSolve solver a
  deriving Functor

pattern Dynamic :: (CPSolve solver `Sub` sig, Functor solver) => solver (Free sig a) -> Free sig a
pattern Dynamic a <- (project -> (Just (Dynamic' a)))
dynamic :: (Functor solver, CPSolve solver `Sub` sig) => solver (Free sig a) -> Free sig a
dynamic = inject . Dynamic'

pattern NewVar k <- (project -> Just (NewVar' k))
exists :: forall solver sig a. (Functor solver, Solver solver, CPSolve solver `Sub` sig) =>
  (Term solver -> Free sig a) -> Free sig a
exists = inject . (NewVar' @solver)
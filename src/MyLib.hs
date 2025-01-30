{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs#-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeOperators #-}


-- {-# LANGUAGE FlexibleInstances#-}
module MyLib
  ( Solver (..),
    CPModel,
    newVar,
    add,
    exist,
    in_domain,
    (@=),
    (@+),
    (@\=),
    (@\==),
    handle,
    exists,
    MyLib.fail,
    try,
    dbs,
    paraHandle,
    addSum,
    evalEffectful,
    dynamic,
    solveDFS,
    solveBFS,
    nbs,
    lds,
  )
where

import Control.Monad.Free (Free (..), MonadFree (wrap))
import FD.OvertonFD as OvertonFD (OConstraint(..), OvertonFD, OPlus (..))
import Solver (Solver(..))
import Prelude hiding (fail)
import Queues (Queue(..))
import Data.Sequence (Seq)



-- | Signature functor for constraint programming model tree
data CPSig solver a where
  NewVar  :: (Term solver -> a) -> CPSig solver a
  Add     :: (Constraint solver) -> a -> CPSig solver a
  Fail    :: CPSig solver a
  Try     :: a -> a -> CPSig solver a
  Dynamic :: solver a -> CPSig solver a

instance Functor solver => Functor (CPSig solver) where
  fmap :: forall a b. (a -> b) -> CPSig solver a -> CPSig solver b
  fmap f (NewVar a)  = NewVar (f . a)
  fmap f (Add c a)   = Add c (f a)
  fmap _ Fail        = Fail
  fmap f (Try l r)   = Try (f l) (f r)
  fmap f (Dynamic s) = Dynamic (fmap f s)

-- | Free Monad over CPSig
type CPModel solver = Free (CPSig solver)

newVar :: Solver solver => CPModel solver (Term solver)
newVar = Free $ NewVar pure

add :: Solver solver => Constraint solver -> CPModel solver ()
add c = Free $ Add c $ pure ()

fail :: Solver solver => CPModel solver a
fail = Free Fail

dynamic :: Solver solver => solver (CPModel solver a) -> CPModel solver a
dynamic s = Free $ Dynamic s

exists :: forall solver a. (Solver solver) => (Term solver -> CPModel solver a) -> CPModel solver a
exists = (>>=) newVar

try :: forall solver a. (Solver solver) => CPModel solver a -> CPModel solver a -> CPModel solver a
try l r = Free $ Try l r

exist :: forall solver a. (Solver solver) => Int ->
  ([Term solver] -> CPModel solver a) -> CPModel solver a
exist n k = go n $ pure []
  where
    go :: Int -> CPModel solver [Term solver] -> CPModel solver a
    go 0 acc = acc >>= k
    go n' acc = do
      v <- newVar
      go (n' - 1) ((v :) <$> acc)

in_domain :: Term OvertonFD -> (Int, Int) -> CPModel OvertonFD ()
v `in_domain` r = add (OInDom v r)

(@=) :: Term OvertonFD -> Int -> CPModel OvertonFD ()
v @= n = add (OHasValue v n)

(@+) :: Term OvertonFD -> Int -> OPlus
(@+) = (:+)

(@\=) :: Term OvertonFD -> Term OvertonFD -> CPModel OvertonFD ()
v1 @\= v2 = add (ODiff v1 v2)

(@\==) :: Term OvertonFD -> OPlus -> CPModel OvertonFD ()
v1 @\== (v2 :+ n) = do
  n' <- newVar
  t2 <- newVar
  add (OHasValue n' n)
  add (OAdd t2 v2 n')
  add (ODiff t2 v1)

addSum :: Term OvertonFD -> Term OvertonFD -> Term OvertonFD -> CPModel OvertonFD ()
addSum a b c = add (OAdd a b c)

handle :: Functor f => (a -> b) -> (f b -> b) -> (Free f a -> b)
handle gen _alg (Pure x) = gen x
handle gen  alg (Free t) = alg (fmap (handle gen alg) t)

paraHandle :: Functor f => (a -> b) -> (f (Free f a, b) -> b) -> (Free f a -> b)
paraHandle gen _alg (Pure x) = gen x
paraHandle gen  alg (Free t) = alg (fmap (\a -> (a, paraHandle gen alg a)) t)

evalEffectful :: forall solver a q. (Solver solver,
  Queue q, Elem q~ (Label solver, CPModel solver a )) =>
  q -> CPModel solver a -> solver [a]
evalEffectful = flip go
  where
    go :: CPModel solver a -> q -> solver [a]
    go = paraHandle (\a wl -> (a:) <$> continue wl) (\case
        NewVar k -> \wl -> do
          v <- newvar
          let (_, k') = k v
          k' wl
        Add c (_, k)  -> \wl -> do
          cond <- addCons c
          if cond then k wl else continue wl
        Fail     -> continue
        Try (_, l) (r, _)  -> \wl -> do
          now <- mark
          l $ pushQ (now,r) wl
        Dynamic d -> \wl -> do
          (_, m) <- d
          m wl
      )
    continue :: q -> solver [a]
    continue wl
      | nullQ wl  = return []
      | otherwise =
        let ((past,t), wl') = popQ wl
        in do
          goto past
          go t wl'


solveDFS :: Solver solver => CPModel solver a -> [a]
solveDFS = run . evalEffectful []

solveBFS :: Solver solver => CPModel solver a -> [a]
solveBFS = run . evalEffectful (emptyQ::Seq a)

dbs :: Solver solver => Int -> CPModel solver a -> CPModel solver a
dbs = flip dbs'
  where
    dbs' :: Solver solver => CPModel solver a -> Int -> CPModel solver a
    dbs' = handle (\ a _ -> pure a) (\case
      Try l r -> \d -> if d > 0 then try (l (d-1)) (r (d-1)) else fail
      other -> \d -> wrap $ ($ d) <$> other
      )

nbs :: Solver solver => Int -> CPModel solver a -> CPModel solver a
nbs = flip nbs'
  where
    nbs' :: Solver solver => CPModel solver a -> Int -> CPModel solver a
    nbs' = handle (\a _ -> pure a) (\case
        Try l r -> \i -> if i > 0 then try (l (i-1)) (r (i-1)) else fail
        other -> \i -> wrap $ ($ i) <$> other
      )

lds :: Solver solver => Int -> CPModel solver a -> CPModel solver a
lds = flip lds'
  where
    lds' :: Solver solver => CPModel solver a -> Int -> CPModel solver a
    lds' = handle (\a _ -> pure a) (\case
        Try l r -> \d -> try (l d) (if d == 0 then fail else r (d-1))
        other   -> \d -> wrap $ ($ d) <$> other
      )

_fs :: forall solver a . Solver solver => CPModel solver a -> CPModel solver a
_fs = undefined


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
{-# LANGUAGE DeriveFunctor #-}


-- {-# LANGUAGE FlexibleInstances#-}
module CPEffects
  ( CPModel,
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
    CPEffects.fail,
    try,
    dbs,
    paraHandle,
    addSum,
    evalEffectful,
    dynamic,
    solveDFS,
    solveBFS,
    lds,
  )
where

import Control.Monad.Free (Free (..), MonadFree (wrap))
import FD.OvertonFD as OvertonFD (OConstraint(..), OvertonFD, OPlus (..))
import Solver (Solver(..))
import Prelude hiding (fail)
import Queues (Queue(..))
import Data.Sequence (Seq)
import Control.Monad (join, when)
import Control.Monad.State (State, MonadState (..), runState, evalState, modify)
import Control.Lens (Profunctor (dimap))
import Data.Kind (Type)



-- | Signature functor for constraint programming model tree
data CPSig solver a where
  NewVar  :: (Term solver -> a) -> CPSig solver a
  Add     :: (Constraint solver) -> a -> CPSig solver a
  Fail    :: CPSig solver a
  Try     :: a -> a -> CPSig solver a
  Dynamic :: solver a -> CPSig solver a

data SearchSig a where
  Try'  :: a -> a -> SearchSig a
  Fail' :: SearchSig a
  deriving Functor

data QueueSig (i :: Type -> Type) (r :: Type) a where
  Push' :: i r -> ir -> a -> QueueSig i r a
  Pop'  :: i r -> a -> QueueSig i r a
  Sol'  :: r -> a -> QueueSig i r a

instance Functor (QueueSig i r) where
  fmap f (Push' i1 i2 k) = Push' i1 i2 (f k)
  fmap f (Pop' i r)      = Pop' i (f r)
  fmap f (Sol' sol rest) = Sol' sol (f rest)

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
        Try (l, _) (r, _)  -> \wl -> do
          now <- mark
          continue $ pushQ (now,l) $ pushQ (now,r) wl
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
dbs = flip go
  where
    go :: Solver solver => CPModel solver a -> Int -> CPModel solver a
    go = handle (\ a _ -> pure a) (\case
      Try l r -> \d -> if d > 0 then try (l (d-1)) (r (d-1)) else fail
      other -> \d -> wrap $ ($ d) <$> other
      )

lds :: Solver solver => Int -> CPModel solver a -> CPModel solver a
lds = flip lds'
  where
    lds' :: Solver solver => CPModel solver a -> Int -> CPModel solver a
    lds' = handle (\a _ -> pure a) (\case
        Try l r -> \d -> try (l d) (if d == 0 then fail else r (d-1))
        other   -> \d -> wrap $ ($ d) <$> other
      )


evalMini :: forall solver a. (Solver solver) => CPModel solver a -> solver (Free SearchSig a)
evalMini = handle (pure . pure) (\case
    NewVar k  -> do
      v <- newvar
      k v
    Add c k   -> do
      success <- addCons c
      if success then k else pure $ Free Fail'
    Dynamic k -> join k
    Fail      -> pure $ Free Fail'
    Try l r   -> do
      now <- mark
      l' <- l
      goto now
      r' <- r
      goto now
      pure $ Free $ Try' l' r'
  )

solveMiniQ :: forall q a. (Queue q, Elem q~ Free SearchSig a) => q -> Free SearchSig a -> [a]
solveMiniQ = flip go
  where
    go :: Free SearchSig a -> q -> [a]
    go (Pure x) q          = x : continue q
    go (Free (Try' l r)) q = continue $ pushQ l $ pushQ r q
    go (Free Fail') q      = continue q
    continue wl
      | nullQ wl  = []
      | otherwise =
        let (t, wl') = popQ wl
        in go t wl'

solvePartialQ :: forall q a.(Queue q, Elem q~ Free SearchSig a) =>
  q -> Free SearchSig a -> Free (QueueSig (Free SearchSig) a) ()
solvePartialQ = flip go
  where
    go :: Free SearchSig a -> q -> Free (QueueSig (Free SearchSig) a) ()
    go (Pure x) wl = Free $ Sol' x (continue wl)
    go (Free t) wl = case t of
      Try' l r -> Free $ Push' l r (continue $ pushQ l $ pushQ r wl)
      Fail'    -> continue wl
    continue :: q -> Free (QueueSig (Free SearchSig) a) ()
    continue wl
      | nullQ wl = pure ()
      | otherwise =
        let (t, wl') = popQ wl
        in Free $ Pop' t (go t wl')

allsols :: Free (QueueSig _i a) () -> [a]
allsols = handle (const []) (\case
    Sol' s k    -> s:k
    Pop' _ k    -> k
    Push' _ _ k -> k
  )

firstsol :: Free (QueueSig _i a) () -> a
firstsol = head . allsols

nbs :: Int -> Free (QueueSig _i a) () -> Free (QueueSig _i a) ()
nbs budget (Pure ()) = Pure ()
nbs budget (Free t)  = case t of
  Sol' s k -> Free $ Sol' s $ nbs budget k
  Pop' n k -> Free $ Pop' n $ nbs budget k
  Push' i1 i2 k -> when (budget > 0) $ Free $ Push' i1 i2 $ nbs (budget - 1) k
solveDFS' model = run $ solveMiniQ [] <$> evalMini model

solveBFS' model = run $ solveMiniQ (emptyQ::Seq a) <$> evalMini model

dbs' :: Int -> Free SearchSig a -> Free SearchSig a
dbs' = flip go
  where
    go :: Free SearchSig a -> Int -> Free SearchSig a
    go = handle (\a _ -> pure a) (\case
        Try' l r -> \d -> if d > 0 then Free $ Try' (l (d-1)) (r (d-1)) else Free Fail'
        other -> \d -> Free $ ($ d) <$> other
      )

-- This doesn't work 
fs :: Free SearchSig a -> Free SearchSig a
fs model = evalState (go model) False
  where
    go :: Free SearchSig a -> State Bool (Free SearchSig a)
    go (Pure x) = do
      put True
      pure $ pure x
    go (Free t) = case t of
      Try' l r -> do
        alreadyFound <- get
        if alreadyFound then pure $ Free Fail' else do
          l' <- go l
          r' <- go r
          pure $ Free $ Try' l' r'
      Fail'    -> pure $ Free Fail'


simpleFs :: forall q a. (Queue q, Elem q~ Free SearchSig a) => q -> Free SearchSig a -> [a]
simpleFs qInit model = evalState (go model qInit) False
  where
    go :: Free SearchSig a -> q -> State Bool [a]
    go (Pure x) q          = do
      put True
      (x:) <$> continue q
    go (Free (Try' l r)) q = continue $ pushQ l $ pushQ r q
    go (Free Fail') q      = continue q
    continue :: q -> State Bool [a]
    continue wl
      | nullQ wl  = pure []
      | otherwise = do
        alreadySols <- get
        if alreadySols then pure [] else
          let (t, wl') = popQ wl
          in go t wl'

solveQueensCount :: Free SearchSig [Int] -> ([[Int]], Int)
solveQueensCount model = runState (go model) 0
  where
    go :: Free SearchSig [Int] -> State Int [[Int]]
    go = handle (\a -> do
      highest <- get
      let h = head a
      when (h > highest) $ put h
      if h > highest then pure [a] else pure []) (\case
        Fail' -> pure []
        Try' l r -> do
          l' <- l
          r' <- r
          pure $ l' <> r'
      )
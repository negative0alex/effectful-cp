{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilyDependencies #-}
module Queues (Queue(..), QueueE, push, pop, pattern Pop, pattern Push) where 
import Data.Kind (Type)
import qualified Data.Sequence
import Data.Sequence (Seq, empty)
import SplitCPEffects (project, Sub, inject, (:+:), getL, putL)
import Control.Monad.Free (Free)

class Queue q where 
  type Elem q :: Type
  
  emptyQ :: q 
  nullQ  :: q -> Bool 
  popQ   :: q -> (Elem q, q)
  pushQ  :: Elem q -> q -> q 


instance Queue [a] where 
  type Elem [a] = a 

  emptyQ :: [a]
  emptyQ = []
  nullQ :: [a] -> Bool
  nullQ = null
  popQ :: [a] -> (Elem [a], [a])
  popQ (h:t) = (h, t)
  pushQ :: Elem [a] -> [a] -> [a]
  pushQ = (:)

instance Queue (Seq a) where 
  type Elem (Seq a) = a

  emptyQ :: Seq a
  emptyQ = empty
  nullQ :: Seq a -> Bool
  nullQ = null
  popQ :: Seq a -> (Elem (Seq a), Seq a)
  popQ (Data.Sequence.viewl -> x Data.Sequence.:< xs) = (x,xs)
  pushQ :: Elem (Seq a) -> Seq a -> Seq a
  pushQ = flip (Data.Sequence.|>)

data QueueE item a where
  Push' :: item -> a -> QueueE item a
  -- Pop'  :: (item -> a) -> QueueE item a
  Pop' :: QueueE item a
  deriving Functor

-- class (Functor qe) => QueueEffect qe where 
--   data Item qe

--   push :: (qe `Sub` sig) => Item qe -> Free sig a -> Free sig a 
--   pop  :: (Functor sig) => Free (qe :+: sig) a

-- instance QueueEffect (QueueE item) where 
--   data Item (QueueE item) = It item 

pattern Push :: (QueueE item `Sub` sig) => item -> Free sig a -> Free sig a
pattern Push i k <- (project -> Just (Push' i k))

push :: (QueueE item `Sub` sig) => item -> Free sig a -> Free sig a 
push i = inject . Push' i

pattern Pop :: (Functor sig) => Free (QueueE item :+: sig) a 
pattern Pop <- (getL -> Just Pop')

pop :: (Functor sig) => Free (QueueE item :+: sig) a 
pop = putL Pop'



-- pattern Pop <- ((project::Free sig a -> Maybe (QueueE item (Free sig a))) -> Just Pop')

-- pop :: forall item sig a. (QueueE item `Sub` sig) => Free sig a 
-- pop = (inject :: QueueE item (Free sig a) -> Free sig a) (Pop' :: QueueE item (Free sig a)) 
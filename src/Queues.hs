{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Queues where 
import Data.Kind (Type)
import qualified Data.Sequence
import Data.Sequence (Seq, empty)

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
  popQ l = (head l, tail l)
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
  
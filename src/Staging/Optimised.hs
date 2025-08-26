{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GADTs #-}

module Staging.Optimised where

import Control.Monad.Free
import Effects.CPSolve
import Effects.NonDet
import Effects.Solver
import FD.OvertonFD
import Transformers (flipT)
import Language.Haskell.TH hiding (Type)
import Queens ((/\))
import Queues
import Solver (Solver (..))
import Staging.Old.Direct (rec2)
import System.Random
import Prelude hiding (fail)
import Eval (SearchTree)
import Data.Kind

showCode :: Code Q a -> IO ()
showCode code = do
  expr <- runQ (unTypeCode (code))
  putStrLn (pprint expr)

data Rep :: Type -> Type where
   Dyn  :: Code Q a -> Rep a   
   Ret :: (Monad m) => Rep a -> Rep (m a)
   Pair :: Rep a -> Rep b -> Rep (a,b)

unRep :: Rep a -> Code Q a 
unRep (Dyn a) = a 
unRep (Ret a) = [|| pure $$(unRep a) ||]
unRep (Pair a b) = [|| ($$(unRep a) , $$(unRep b)) ||]

pairR :: Rep a -> Rep b -> Rep (a,b)
pairR = Pair

letR :: Rep (a,b) -> (Rep a -> Rep b -> Rep c) -> Rep c 
letR (Pair a b) cont = cont a b
letR (Dyn pair) cont = Dyn [|| let (a,b) = $$pair in $$(unRep $ cont (Dyn [|| a ||]) (Dyn [|| b ||]))||] 

pureR :: (Monad m) => Rep a -> Rep (m a)
pureR = Ret

bindR :: (Monad m) => Rep (m a) -> (Rep a -> Rep (m b)) -> Rep (m b)
bindR (Dyn ma) f = Dyn $ [|| $$ma >>= \a -> $$(unRep $ f (Dyn [|| a ||])) ||]
bindR (Ret a) f = f a

(>>=>) :: (Monad m) => Rep (m a) -> (Rep a -> Rep (m b)) -> Rep (m b)
(>>=>) = bindR
infixl 1 >>=>

unitR :: Rep ()
unitR = Dyn [|| () ||]

zeroR :: Rep Int 
zeroR = Dyn [|| 0 ||]

newtype ContRep s = R {r :: forall b. (s -> Rep b) -> Rep b}

instance Functor (ContRep) where 
  fmap :: (a -> b) -> ContRep a -> ContRep b
  fmap f (R ka) = R $ \kb -> ka $ \a -> kb (f a)

instance Applicative (ContRep) where 
  pure :: a -> ContRep a
  pure a = R $ (flip ($) a)

  (<*>) :: ContRep (a -> b) -> ContRep a -> ContRep b
  (R kf) <*> (R ka) = R $ \kb -> kf $ \f -> ka $ \a -> kb (f a)

instance Monad (ContRep) where 
  (>>=) :: ContRep a -> (a -> ContRep b) -> ContRep b
  (R kf) >>= f = R $ \k -> kf $ \a -> r (f a) k

newtype StateTransform state solver = ST {unST :: (Rep state -> Rep (solver state))}

newtype NextTransform ts es solver a
  = NT
  { unNT ::
      Rep ts ->
      Rep es ->
      Rep (SearchTree solver a) ->
      (Rep ts, Rep es, Rep (SearchTree solver a))
  }

idState :: (Solver solver) => StateTransform state solver
idState = ST $ pureR

liftST :: (Monad solver) => (Code Q a -> Code Q a) -> StateTransform a solver 
liftST f = ST $ \ra -> pureR . Dyn $ f (unRep ra)

crossST :: Monad solver => StateTransform s1 solver -> StateTransform s2 solver -> StateTransform (s1, s2) solver 
crossST st1 st2 = ST $ \s -> letR s $ \s1 s2 -> 
          (unST $ st1) s1 >>=> \s1' -> 
            (unST $ st2) s2 >>=> \s2' -> 
              pureR $ pairR s1' s2'


data (Solver solver) => SearchTransformer ts es solver a = SearchTransformer
  { tsInit :: Rep ts
  , esInit :: Rep es
  , leftTs :: StateTransform ts solver
  , rightTs :: StateTransform ts solver
  , solEs :: StateTransform es solver
  , nextState :: NextTransform ts es solver a
  }

dbsTrans :: (Solver solver) => Int -> SearchTransformer Int () solver a
dbsTrans depthLimit =
  SearchTransformer
    { tsInit = zeroR
    , esInit = unitR
    , solEs = idState
    , leftTs = liftST $ \a -> [|| $$a + 1 ||]
    , rightTs = liftST $ \a -> [|| $$a + 1 ||]
    , nextState = NT $ \ts es model -> (ts, es, Dyn [||if $$(unRep ts) <= depthLimit then $$(unRep model) else fail||])
    }

-- branch and bound scaffolding

type Bound solver a = (SearchTree solver a) -> (SearchTree solver a)

type NewBound solver a = Rep (solver (Bound solver a))

data BBEvalState solver a = BBP Int (Bound solver a)

bbNB ::
  forall a solver.
  (Solver solver) =>
  NewBound solver a ->
  SearchTransformer Int (BBEvalState solver a) solver a
bbNB newBound =
  SearchTransformer
    { tsInit = zeroR
    , esInit = Dyn [|| BBP 0 id ||]
    , solEs = 
      ST $ \es -> newBound >>=> \bound -> pureR $ Dyn [|| let (BBP v _) = $$(unRep es) in BBP (v+1) $$(unRep bound)||]
    , leftTs = idState
    , rightTs = idState
    , nextState = NT @Int @(BBEvalState solver a) @solver $ \ts es tree ->
        ( Dyn [||
          let (BBP nv _) = $$(unRep es)
              v = $$(unRep ts)
           in if nv > v then nv else v
          ||]
        , es
        , Dyn [||
          let (BBP nv bound) = $$(unRep es)
              v = $$(unRep ts)
           in if nv > v
                then bound $$(unRep tree)
                else $$(unRep tree)
          ||]
        )
    }

newBound :: forall a. NewBound OvertonFD a
newBound =
  Dyn [||
  do
    obj <- fd_objective
    dom <- fd_domain $ obj
    let val = head dom
    return ((\tree -> obj @< val /\ tree))
  ||]

bbS :: SearchTransformer Int (BBEvalState OvertonFD a) OvertonFD a
bbS = bbNB newBound

ldsS :: (Solver solver) => Int -> SearchTransformer Int () solver a
ldsS discLimit =
  SearchTransformer
    { tsInit = zeroR
    , esInit = unitR
    , solEs = idState
    , leftTs = idState
    , rightTs = liftST $ \a -> [|| $$a + 1 ||]
    , nextState = NT $ \disc u tree ->
        ( disc
        , u
        , Dyn [||if $$(unRep disc) <= discLimit then $$(unRep tree) else fail||]
        )
    }

randS :: (Solver solver) => Int -> SearchTransformer () [Bool] solver a
randS seed =
  SearchTransformer
    { tsInit = unitR
    , esInit = Dyn [|| randoms $ mkStdGen seed ||]
    , solEs = idState
    , leftTs = idState
    , rightTs = idState
    , nextState = NT $ \u coins tree ->
        ( u
        , Dyn [||tail $$(unRep coins)||]
        , Dyn [||let tree' = $$(unRep tree) in if head $$(unRep coins) then flipT tree' else tree'||]
        )
    }

stage ::
  forall solver q ts es a.
  ( Solver solver
  , Queue q
  , Elem q ~ (Label solver, ts, SearchTree solver a)
  ) =>
  SearchTransformer ts es solver a ->
  Code Q (q -> SearchTree solver a -> solver [a])
stage (SearchTransformer tsInit esInit leftTs rightTs solEs nextState) =
  rec2
    ( \(go, continue) ->
        [||
        \ts es q tree -> case tree of
          Pure a -> do
            es' <- $$(unRep $ unST solEs $ Dyn [||es||])
            (a :) <$> ($$continue es' q)
          l :|: r -> do
            now <- mark
            tsL <- $$(unRep $ unST leftTs $ Dyn [||ts||])
            tsR <- $$(unRep $ unST rightTs $ Dyn [||ts||])
            $$continue es (pushQ (now, tsL, l) $ pushQ (now, tsR, r) q)
          Fail -> $$continue es q
          (Add c k) -> do
            success <- addCons c
            if success then $$go ts es q k else $$continue es q
          (NewVar k) -> do
            var <- newvar
            $$go ts es q (k var)
          (Dynamic k) -> do
            term <- k
            $$go ts es q term
          (Solver s) -> s >>= \term -> $$go ts es q term
        ||]
    )
    ( \(go, _) ->
        [||
        \es q ->
          if nullQ q
            then pure []
            else
              let ((label, ts, tree), q') = popQ q
               in $$( let (ts', es', tree') = unNT nextState (Dyn [||ts||]) (Dyn [||es||]) (Dyn [||tree||])
                       in [||$$go $$(unRep ts') $$(unRep es') q' ((solve $ goto label) >> $$(unRep tree'))||]
                    )
        ||]
    )
    (\(go, _) -> [||$$go $$(unRep tsInit) $$(unRep esInit)||])

composeTrans ::
  (Solver solver) =>
  SearchTransformer ts1 es1 solver a ->
  SearchTransformer ts2 es2 solver a ->
  SearchTransformer (ts1, ts2) (es1, es2) solver a
composeTrans t1 t2 =
  SearchTransformer
    { tsInit = pairR (tsInit t1) (tsInit t2)
    , esInit = pairR (esInit t1) (esInit t2)
    , leftTs = crossST (leftTs t1) (leftTs t2)
    , rightTs = crossST (rightTs t1) (rightTs t2)
    , solEs = crossST (solEs t1) (solEs t2)
    , nextState = NT $ \ts es tree -> undefined
        -- let ts1 = [||fst $$ts||]
        --     ts2 = [||snd $$ts||]
        --     es1 = [||fst $$es||]
        --     es2 = [||snd $$es||]
        --     (ts1', es1', tree') = unNT (nextState t1) ts1 es1 tree
        --     (ts2', es2', tree'') = unNT (nextState t2) ts2 es2 tree'
        --  in ([||($$ts1', $$ts2')||], [||($$es1', $$es2')||], tree'')
    }

(%&) ::
  (Solver solver) =>
  SearchTransformer ts1 es1 solver a ->
  SearchTransformer ts2 es2 solver a ->
  SearchTransformer (ts1, ts2) (es1, es2) solver a
(%&) = composeTrans
infixr 6 %&

---------------------------------------------------

bbLdsRandS :: Int -> Int -> SearchTransformer (((), (Int, Int))) (([Bool], ((), BBEvalState OvertonFD a))) OvertonFD a
bbLdsRandS seed discrepancy = (randS seed) %& (ldsS discrepancy) %& bbS

bbLdsRandCode ::
  Int -> Int -> Code
    Q
    ( [(Label OvertonFD, ((), (Int, Int)), SearchTree OvertonFD a)] ->
      SearchTree OvertonFD a ->
      OvertonFD [a]
    )
bbLdsRandCode seed discrepancy = stage (bbLdsRandS seed discrepancy)

justBBCode :: Code Q ([(Label OvertonFD, Int, SearchTree OvertonFD a)] -> SearchTree OvertonFD a -> OvertonFD [a])
justBBCode = stage bbS
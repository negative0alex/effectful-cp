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
module Staging.IncrementalOptimisation3 where
import Data.Kind
import Control.Monad.Free
import Effects.Core
import Language.Haskell.TH hiding (Type)
import Effects.NonDet
import Staging.Handlers (rec2, codeCurry)
import Prelude hiding (fail)
import Queues (Queue, Elem, pushQ, nullQ, popQ)
import System.Random
import Handlers (flipT)

-- move over to CPS and finish inserting let-bindings

showCode :: Code Q a -> IO ()
showCode code = do expr <- runQ (unTypeCode (code))
                   putStrLn (pprint expr)

type Rep a = Code Q a

fstP :: Rep (a,b) -> Rep a 
fstP t = [|| fst $$t ||]

sndP :: Rep (a,b) -> Rep b 
sndP t = [|| snd $$t ||]

pairP :: Rep a -> Rep b -> Rep (a,b)
pairP a b = [|| ($$a, $$b) ||]

let_ :: Rep (a,b) -> (Rep a -> Rep b -> Rep c) -> Rep c 
let_ p k = [|| let (a,b) = $$p in $$(k [||a||] [||b||]) ||]

data StateTransform state = 
  IdState 
  | TransState (forall b. Rep state -> (Rep state -> Rep b) -> Rep b)

getTrans :: StateTransform state -> (Rep state -> (Rep state -> Rep b) -> Rep b)
getTrans IdState = flip ($)
getTrans (TransState f) = f

data NextTransform ts es = 
    FullT (forall a b. Rep ts -> Rep es -> Rep (Free (NonDet :+: Void) a) ->
        (Rep ts -> Rep es -> Rep (Free (NonDet :+: Void) a) -> Rep b) -> Rep b)
  | OnlyTsT (forall a b. Rep ts -> Rep es -> Rep (Free (NonDet :+: Void) a) ->
        (Rep ts -> Rep (Free (NonDet :+: Void) a) -> Rep b) -> Rep b)
  | OnlyEsT (forall a b. Rep ts -> Rep es -> Rep (Free (NonDet :+: Void) a) ->
        (Rep es -> Rep (Free (NonDet :+: Void) a) -> Rep b) -> Rep b)
  | NoneT (forall a b. Rep ts -> Rep es -> Rep (Free (NonDet :+: Void) a) ->
        (Rep (Free (NonDet :+: Void) a) -> Rep b) -> Rep b)

getNextTransform :: NextTransform ts es -> 
  (forall b. Rep ts -> Rep es -> Rep (Free (NonDet :+: Void) a) ->
        (Rep ts -> Rep es -> Rep (Free (NonDet :+: Void) a) -> Rep b) -> Rep b)
getNextTransform (FullT f)   = f 
getNextTransform (OnlyTsT f) = \ts es tree k' -> f ts es tree (\ts' tree' -> k' ts' es tree')
getNextTransform (OnlyEsT f) = \ts es tree k' -> f ts es tree (\es' tree' -> k' ts es' tree')
getNextTransform (NoneT f)   = \ts es tree k' -> f ts es tree (\tree' -> k' ts es tree')

data SearchTransformer' ts es = SearchTransformer' 
  { tsInit' :: Rep ts,
    esInit' :: Rep es,
    leftTs' :: StateTransform ts,
    rightTs' :: StateTransform ts,
    nextState' :: NextTransform ts es
  }

dbsTrans' :: Int -> SearchTransformer' Int () 
dbsTrans' depthLimit = SearchTransformer' 
  { tsInit' = [|| 0 ||]
  , esInit' = [|| () ||]
  , leftTs' = TransState $ \ts k -> k [|| $$ts + 1 ||]
  , rightTs' = TransState $ \ts k -> k [|| $$ts + 1 ||]
  , nextState' = NoneT $ \ts _ tree k -> k [|| if $$ts <= depthLimit then $$tree else fail ||]
  }

nbsTrans' :: Int -> SearchTransformer' () Int 
nbsTrans' nodeLimit = 
  SearchTransformer'
    { tsInit' = [|| () ||]
    , esInit' = [|| 0 ||]
    , leftTs' = IdState
    , rightTs' = IdState
    , nextState' = OnlyEsT $ \_ es tree k -> 
      k [|| $$es + 1 ||] [|| if $$es <= nodeLimit then $$tree else fail ||]
    }

randTrans' :: Int -> SearchTransformer' () [Bool]
randTrans' seed = SearchTransformer' 
  { tsInit' = [|| () ||]
  , esInit' = [|| randoms $ mkStdGen seed ||]
  , leftTs' = IdState
  , rightTs' = IdState 
  , nextState' = OnlyEsT $ \_ es tree k -> k [|| tail $$es ||]
    [|| let tree' = $$tree in if head $$es then flipT tree' else tree' ||]
  }

composeTrans' :: SearchTransformer' ts1 es1 -> 
  SearchTransformer' ts2 es2 -> 
  SearchTransformer' (ts1, ts2) (es1, es2)
composeTrans' t1 t2 = SearchTransformer' 
  { tsInit' = [|| ($$(tsInit' t1), $$(tsInit' t2)) ||]
  , esInit' = [|| ($$(esInit' t1), $$(esInit' t2)) ||]  
  , leftTs' = case (leftTs' t1, leftTs' t2) of 
      (IdState, IdState) -> IdState 
      (f1, f2) -> TransState $ \ts k -> let_ ts $ \tsL tsR -> 
        (getTrans f1 tsL) $ \tsL' -> (getTrans f2 tsR) $ \tsR' -> k $ pairP tsL' tsR' 
  , rightTs' = case (rightTs' t1, rightTs' t2) of 
      (IdState, IdState) -> IdState 
      (f1, f2) -> TransState $ \ts k -> let_ ts $ \tsL tsR -> 
        (getTrans f1 tsL) $ \tsL' -> (getTrans f2 tsR) $ \tsR' -> k $ pairP tsL' tsR'
  , nextState' = case (nextState' t1, nextState' t2) of 
      -- both get identity
        (NoneT f1, NoneT f2) -> NoneT $ 
          \ts es tree k -> let_ ts $ \tsL tsR -> let_ es $ \esL esR -> 
            f1 tsL esL tree $ \tree' -> 
            f2 tsR esR tree' $ \tree'' -> k tree''
        -- es gets identity
        (NoneT f1, OnlyTsT f2) -> OnlyTsT $ 
          \ts es tree k -> let_ ts $ \tsL tsR -> let_ es $ \esL esR -> 
            f1 tsL esL tree $ \tree' -> 
            f2 tsR esR tree' $ \tsR' tree'' -> k (pairP tsL tsR') tree''
        (OnlyTsT f1, NoneT f2) -> OnlyTsT $ 
          \ts es tree k -> let_ ts $ \tsL tsR -> let_ es $ \esL esR -> 
            f1 tsL esL tree $ \tsL' tree' -> 
            f2 tsR esR tree' $ \tree'' -> k (pairP tsL' tsR) tree''
        (OnlyTsT f1, OnlyTsT f2) -> OnlyTsT $ 
          \ts es tree k -> let_ ts $ \tsL tsR -> let_ es $ \esL esR -> 
            f1 tsL esL tree $ \tsL' tree' -> 
            f2 tsR esR tree' $ \tsR' tree'' -> k (pairP tsL' tsR') tree''
        -- ts gets identity
        (NoneT f1, OnlyEsT f2) -> OnlyEsT $ 
          \ts es tree k -> let_ ts $ \tsL tsR -> let_ es $ \esL esR -> 
            f1 tsL esL tree $ \tree' -> 
            f2 tsR esR tree' $ \esR' tree'' -> k (pairP esL esR') tree''
        (OnlyEsT f1, NoneT f2) -> OnlyEsT $ 
          \ts es tree k -> let_ ts $ \tsL tsR -> let_ es $ \esL esR -> 
            f1 tsL esL tree $ \esL' tree' -> 
            f2 tsR esR tree' $ \tree'' -> k (pairP esL' esR) tree''
        (OnlyEsT f1, OnlyEsT f2) -> OnlyEsT $ 
          \ts es tree k -> let_ ts $ \tsL tsR -> let_ es $ \esL esR -> 
            f1 tsL esL tree $ \esL' tree' -> 
            f2 tsR esR tree' $ \esR' tree'' -> k (pairP esL' esR') tree''
        -- neither gets identity
        (f1T, f2T) -> FullT $ \ts es tree k ->
          let f1 = getNextTransform f1T 
              f2 = getNextTransform f2T 
              in 
                let_ ts $ \tsL tsR -> let_ es $ \esL esR -> 
                  f1 tsL esL tree $ \tsL' esL' tree' -> 
                    f2 tsR esR tree' $ \tsR' esR' tree'' ->
                      k (pairP tsL' tsR') (pairP esL' esR') tree''
}

stage' :: forall q ts es a. (Queue q, Elem q ~ (ts, Free (NonDet :+: Void) a)) =>
  SearchTransformer' ts es -> 
  Code Q (q -> Free (NonDet :+: Void) a -> Free Void [a])
stage' (SearchTransformer' tsInit esInit leftTs rightTs nextState) = rec2 
  (\(_, continue) ->  
    [||
    \ts es q tree -> case tree of 
      Pure a -> (a:) <$> $$continue es q
      l :|: r -> $$((getTrans leftTs [|| ts ||]) $ \tsL -> (getTrans rightTs [|| ts ||]) $ \tsR -> 
        [|| $$continue es (pushQ ($$tsL, l) $ pushQ ($$tsR, r) q)||])
      Fail -> $$continue es q
    ||]
    )
  (\(go, _) -> [||
    \es q -> if nullQ q then pure [] else
      let ((ts, tree),q') = popQ q in
        $$(
          getNextTransform nextState [||ts||] [||es||] [||tree||] $ 
          \ts' es' tree' -> [|| $$go $$ts' $$es' q' $$tree' ||]
          )
  ||])
  (\(go, _) -> [|| $$go $$tsInit $$esInit ||])

exampleTrans :: SearchTransformer' ((Int, ()), ()) (((), [Bool]), Int)
exampleTrans = composeTrans' (composeTrans' (dbsTrans' 15) (randTrans' 300)) (nbsTrans' 1500)

stagedExample :: Code Q ([(((Int, ()), ()), Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
stagedExample = stage' exampleTrans

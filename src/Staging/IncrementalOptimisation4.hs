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
module Staging.IncrementalOptimisation4 where
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

data Rep :: Type -> Type where
   Pair :: Rep a -> Rep b -> Rep (a, b)
   Dyn  :: Code Q a -> Rep a   

dynP :: Rep a -> Code Q a
dynP (Pair l r) = [|| ($$(dynP l), $$(dynP r)) ||]
dynP (Dyn p) = p

let_ :: Rep (a, b) -> (Rep a -> Rep b -> Rep c) -> Rep c
let_ (Pair l r) k = k l r
let_ (Dyn p) k = Dyn [|| let (a, b) = $$p in $$(dynP (k (Dyn [||a||]) (Dyn [||b||]))) ||]

data StateTransform state = 
  IdState 
  | TransState (forall b. Rep state -> (Rep state -> Rep b) -> Rep b)

getTrans :: StateTransform state -> (Rep state -> (Rep state -> Rep b) -> Rep b)
getTrans IdState = flip ($)
getTrans (TransState f) = f

data StateTransform2 state = 
  IdState2
  | TransState2 (forall r. Rep state -> (Rep state -> Rep state -> Rep r) -> Rep r)

getTrans2 :: StateTransform2 state -> (forall r. Rep state -> (Rep state -> Rep state -> Rep r) -> Rep r) 
getTrans2 (TransState2 k) = k
getTrans2 IdState2 = \s k -> k s s

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
    leftTs' :: StateTransform2 ts,
    rightTs' :: StateTransform ts,
    nextState' :: NextTransform ts es
  }

dbsTrans' :: Int -> SearchTransformer' Int () 
dbsTrans' depthLimit = SearchTransformer' 
  { tsInit' = Dyn [|| 0 ||]
  , esInit' = Dyn [|| () ||]
  , leftTs' = TransState2 $ \ts k -> k (Dyn [|| $$(dynP ts) + 1 ||]) ts
  , rightTs' = TransState $ \ts k -> k (Dyn [|| $$(dynP ts) + 1 ||])
  , nextState' = NoneT $ \ts _ tree k -> k (Dyn [|| if $$(dynP ts) <= depthLimit then $$(dynP tree) else fail ||])
  }

nbsTrans' :: Int -> SearchTransformer' () Int 
nbsTrans' nodeLimit = 
  SearchTransformer'
    { tsInit' = Dyn [|| () ||]
    , esInit' = Dyn [|| 0 ||]
    , leftTs' = IdState2
    , rightTs' = IdState
    , nextState' = OnlyEsT $ \_ es tree k -> 
      k (Dyn [|| $$(dynP es) + 1 ||]) (Dyn [|| if $$(dynP es) <= nodeLimit then $$(dynP tree) else fail ||])
    }

randTrans' :: Int -> SearchTransformer' () [Bool]
randTrans' seed = SearchTransformer' 
  { tsInit' = Dyn [|| () ||]
  , esInit' = Dyn [|| randoms $ mkStdGen seed ||]
  , leftTs' = IdState2
  , rightTs' = IdState 
  , nextState' = OnlyEsT $ \_ es tree k -> k (Dyn [|| tail $$(dynP es) ||])
    (Dyn [|| let tree' = $$(dynP tree) in if head $$(dynP es) then flipT tree' else tree' ||])
  }

composeTrans' :: SearchTransformer' ts1 es1 -> 
  SearchTransformer' ts2 es2 -> 
  SearchTransformer' (ts1, ts2) (es1, es2)
composeTrans' t1 t2 = SearchTransformer' 
  { tsInit' = Dyn [|| ($$(dynP $ tsInit' t1), $$(dynP $ tsInit' t2)) ||]
  , esInit' = Dyn [|| ($$(dynP $ esInit' t1), $$(dynP $ esInit' t2)) ||]  
  , leftTs' = case (leftTs' t1, leftTs' t2) of 
      (IdState2, IdState2) -> IdState2
      (f1, f2) -> TransState2 $ \ts k -> let_ ts $ \tsL tsR -> 
        (getTrans2 f1 tsL) $ \tsL' tsL0 -> (getTrans2 f2 tsR) $ \tsR' tsR0 -> k (Pair tsL' tsR') (Pair tsL0 tsR0)
  , rightTs' = case (rightTs' t1, rightTs' t2) of 
      (IdState, IdState) -> IdState 
      (f1, f2) -> TransState $ \ts k -> let_ ts $ \tsL tsR -> 
        (getTrans f1 tsL) $ \tsL' -> (getTrans f2 tsR) $ \tsR' -> k $ Pair tsL' tsR'
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
            f2 tsR esR tree' $ \tsR' tree'' -> k (Pair tsL tsR') tree''
        (OnlyTsT f1, NoneT f2) -> OnlyTsT $ 
          \ts es tree k -> let_ ts $ \tsL tsR -> let_ es $ \esL esR -> 
            f1 tsL esL tree $ \tsL' tree' -> 
            f2 tsR esR tree' $ \tree'' -> k (Pair tsL' tsR) tree''
        (OnlyTsT f1, OnlyTsT f2) -> OnlyTsT $ 
          \ts es tree k -> let_ ts $ \tsL tsR -> let_ es $ \esL esR -> 
            f1 tsL esL tree $ \tsL' tree' -> 
            f2 tsR esR tree' $ \tsR' tree'' -> k (Pair tsL' tsR') tree''
        -- ts gets identity
        (NoneT f1, OnlyEsT f2) -> OnlyEsT $ 
          \ts es tree k -> let_ ts $ \tsL tsR -> let_ es $ \esL esR -> 
            f1 tsL esL tree $ \tree' -> 
            f2 tsR esR tree' $ \esR' tree'' -> k (Pair esL esR') tree''
        (OnlyEsT f1, NoneT f2) -> OnlyEsT $ 
          \ts es tree k -> let_ ts $ \tsL tsR -> let_ es $ \esL esR -> 
            f1 tsL esL tree $ \esL' tree' -> 
            f2 tsR esR tree' $ \tree'' -> k (Pair esL' esR) tree''
        (OnlyEsT f1, OnlyEsT f2) -> OnlyEsT $ 
          \ts es tree k -> let_ ts $ \tsL tsR -> let_ es $ \esL esR -> 
            f1 tsL esL tree $ \esL' tree' -> 
            f2 tsR esR tree' $ \esR' tree'' -> k (Pair esL' esR') tree''
        -- neither gets identity
        (f1T, f2T) -> FullT $ \ts es tree k ->
          let f1 = getNextTransform f1T 
              f2 = getNextTransform f2T 
              in 
                let_ ts $ \tsL tsR -> let_ es $ \esL esR -> 
                  f1 tsL esL tree $ \tsL' esL' tree' -> 
                    f2 tsR esR tree' $ \tsR' esR' tree'' ->
                      k (Pair tsL' tsR') (Pair esL' esR') tree''
}

stage' :: forall q ts es a. (Queue q, Elem q ~ (ts, Free (NonDet :+: Void) a)) =>
  SearchTransformer' ts es -> 
  Code Q (q -> Free (NonDet :+: Void) a -> Free Void [a])
stage' (SearchTransformer' tsInit esInit leftTs rightTs nextState) = rec2 
  (\(_, continue) ->  
    [||
    \ts es q tree -> case tree of 
      Pure a -> (a:) <$> $$continue es q
      l :|: r -> $$(dynP $ (getTrans2 leftTs (Dyn [|| ts ||])) $ \tsL ts0 -> (getTrans rightTs ts0) $ \tsR -> 
        Dyn [|| $$continue es (pushQ ($$(dynP tsL), l) $ pushQ ($$(dynP tsR), r) q)||])
      Fail -> $$continue es q
    ||]
    )
  (\(go, _) -> [||
    \es q -> if nullQ q then pure [] else
      let ((ts, tree),q') = popQ q in
        $$(dynP $ 
          getNextTransform nextState (Dyn [||ts||]) (Dyn [||es||]) (Dyn [||tree||]) $ 
          \ts' es' tree' -> Dyn [|| $$go $$(dynP ts') $$(dynP es') q' $$(dynP tree') ||]
          )
  ||])
  (\(go, _) -> [|| $$go $$(dynP tsInit) $$(dynP esInit) ||])

exampleTrans :: SearchTransformer' ((Int, ()), ()) (((), [Bool]), Int)
exampleTrans = composeTrans' (composeTrans' (dbsTrans' 15) (randTrans' 300)) (nbsTrans' 1500)

stagedExample :: Code Q ([(((Int, ()), ()), Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
stagedExample = stage' exampleTrans

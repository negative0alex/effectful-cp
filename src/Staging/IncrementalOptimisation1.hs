{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Staging.IncrementalOptimisation1 where

import Control.Monad.Free
import Data.Kind
import Effects.Core
import Effects.NonDet
import Handlers (flipT)
import Language.Haskell.TH hiding (Type)
import Queues (Elem, Queue, nullQ, popQ, pushQ)
import Staging.Handlers (codeCurry, rec2)
import System.Random
import Prelude hiding (fail)

-- remove redundant tuple operations for identity transforms

showCode :: Code Q a -> IO ()
showCode code = do
  expr <- runQ (unTypeCode (code))
  putStrLn (pprint expr)

type Rep a = Code Q a

fstP :: Rep (a, b) -> Rep a
fstP t = [||fst $$t||]

sndP :: Rep (a, b) -> Rep b
sndP t = [||snd $$t||]

pairP :: Rep a -> Rep b -> Rep (a, b)
pairP a b = [||($$a, $$b)||]

data StateTransform state
  = IdState
  | TransState (Rep state -> Rep state)

getTrans :: StateTransform state -> (Rep state -> Rep state)
getTrans IdState = id
getTrans (TransState f) = f

type (~>) s a = s -> (s, a)

type (~>?) s a = s -> (Maybe s, a)

newtype NextTransform ts es
  = NT ( forall a.
        Rep ts -> Rep es ->
        Rep (Free (NonDet :+: Void) a) ->
        ( Maybe (Rep ts), Maybe (Rep es),
          Rep (Free (NonDet :+: Void) a)
        ))

getNextTransform ::
  NextTransform ts es ->
  Rep ts ->
  Rep es ->
  Rep (Free (NonDet :+: Void) a) ->
  (Rep ts, Rep es, Rep (Free (NonDet :+: Void) a))
getNextTransform (NT f) = \ts es tree ->
  let (ts', es', tree') = f ts es tree
   in ( maybe ts id ts',
        maybe es id es',
        tree'
      )

noneT :: (forall a. Rep ts -> Rep es -> (Rep (Free (NonDet :+: Void) a)) -> (Rep (Free (NonDet :+: Void) a))) -> 
    NextTransform ts es
noneT f = NT $ \ts es tree -> (Nothing, Nothing, f ts es tree)

onlyEsT :: (forall a. Rep ts -> Rep es -> (Rep (Free (NonDet :+: Void) a)) -> (Rep es, (Rep (Free (NonDet :+: Void) a)))) -> 
  NextTransform ts es
onlyEsT f = NT $ \ts es tree -> let (es', tree') = f ts es tree in (Nothing, Just es', tree')

data SearchTransformer ts es = SearchTransformer
  { tsInit :: Rep ts,
    esInit :: Rep es,
    leftTs :: StateTransform ts,
    rightTs :: StateTransform ts,
    nextState :: NextTransform ts es
  }

dbsTrans :: Int -> SearchTransformer Int ()
dbsTrans depthLimit =
  SearchTransformer
    { tsInit = [||0||],
      esInit = [||()||],
      leftTs = TransState $ \ts -> [||$$ts + 1||],
      rightTs = TransState $ \ts -> [||$$ts + 1||]
      , nextState = noneT $ \ts _ tree -> [|| if $$ts <= depthLimit then $$tree else fail ||]
    }

nbsTrans :: Int -> SearchTransformer () Int
nbsTrans nodeLimit =
  SearchTransformer
    { tsInit = [||()||],
      esInit = [||0||],
      leftTs = IdState,
      rightTs = IdState
      , nextState = onlyEsT $ \_ es tree ->
        ([|| $$es + 1 ||], [|| if $$es <= nodeLimit then $$tree else fail ||])
    }

randTrans :: Int -> SearchTransformer () [Bool]
randTrans seed =
  SearchTransformer
    { tsInit = [||()||],
      esInit = [||randoms $ mkStdGen seed||],
      leftTs = IdState,
      rightTs = IdState
      , nextState = onlyEsT $ \_ es tree -> ([|| tail $$es ||],
        [|| let tree' = $$tree in if head $$es then flipT tree' else tree' ||])
    }

pairMaybe :: Rep a -> Rep b -> Maybe (Rep a) -> Maybe (Rep b) -> Maybe (Rep (a, b))
pairMaybe defA defB a b = case (a,b) of 
  (Nothing, Nothing) -> Nothing 
  (a, b) -> Just $ pairP (maybe defA id a) (maybe defB id b)

composeTrans ::
  SearchTransformer ts1 es1 ->
  SearchTransformer ts2 es2 ->
  SearchTransformer (ts1, ts2) (es1, es2)
composeTrans t1 t2 =
  SearchTransformer
    { tsInit = [||($$(tsInit t1), $$(tsInit t2))||],
      esInit = [||($$(esInit t1), $$(esInit t2))||],
      leftTs = case (leftTs t1, leftTs t2) of
        (IdState, IdState) -> IdState
        (f1, f2) -> TransState $ \ts ->
          pairP (getTrans f1 (fstP ts)) (getTrans f2 (sndP ts)),
      rightTs = case (rightTs t1, rightTs t2) of
        (IdState, IdState) -> IdState
        (f1, f2) -> TransState $ \ts ->
          pairP (getTrans f1 (fstP ts)) (getTrans f2 (sndP ts)),
      nextState = let 
        (NT f1) = nextState t1 
        (NT f2) = nextState t2 in NT $ \tsP esP tree -> 
            let (tsL', esL', tree') = f1 (fstP tsP) (fstP esP) tree  
                (tsR', esR', tree'') = f2 (sndP tsP) (sndP esP) tree' 
            in (pairMaybe (fstP tsP) (sndP tsP) tsL' tsR',
                pairMaybe (fstP esP) (sndP esP) esL' esR',
                tree'')
    }

stage ::
  forall q ts es a.
  (Queue q, Elem q ~ (ts, Free (NonDet :+: Void) a)) =>
  SearchTransformer ts es ->
  Code Q (q -> Free (NonDet :+: Void) a -> Free Void [a])
stage (SearchTransformer tsInit esInit leftTs rightTs nextState) =
  rec2
    ( \(_, continue) ->
        [||
        \ts es q tree -> case tree of
          Pure a -> (a :) <$> $$continue es q
          l :|: r -> $$continue es (pushQ ($$(getTrans leftTs [||ts||]), l) $ pushQ ($$(getTrans rightTs [||ts||]), r) q)
          Fail -> $$continue es q
        ||]
    )
    ( \(go, _) ->
        [||
        \es q ->
          if nullQ q
            then pure []
            else
              let ((ts, tree), q') = popQ q
               in $$( let (ts', es', tree') = getNextTransform nextState [||ts||] [||es||] [||tree||]
                       in [||$$go $$ts' $$es' q' $$tree'||]
                    )
        ||]
    )
    (\(go, _) -> [||$$go $$tsInit $$esInit||])

exampleTrans :: SearchTransformer ((Int, ()), ()) (((), [Bool]), Int)
exampleTrans = composeTrans (composeTrans (dbsTrans 15) (randTrans 300)) (nbsTrans 1500)

stagedExample :: Code Q ([(((Int, ()), ()), Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
stagedExample = stage exampleTrans

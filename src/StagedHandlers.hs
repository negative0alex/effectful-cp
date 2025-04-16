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
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module StagedHandlers where

import Control.Monad.Free
import Effects
import Language.Haskell.TH hiding (dyn)
import NonDet
import Queues
import Prelude hiding (fail)
import Data.Bifunctor (Bifunctor(bimap))

codeCurry :: (CodeQ a -> CodeQ b) -> CodeQ (a -> b)
codeCurry f = [||\a -> $$(f [||a||])||]

data Value a where 
  Atomic :: Code Q a -> Value a 
  Pair :: Value a -> Value b -> Value (a,b)

dyn :: Value a -> Code Q a 
dyn (Atomic a) = a 
dyn (Pair a b) = [|| ($$(dyn a), $$(dyn b)) ||]

data SearchTransformer ts es = SearchTransformer
  { tsInit :: Code Q ts,
    esInit :: Code Q es,
    solEs :: forall b. Code Q es -> (Code Q es -> Code Q b) -> Code Q b,
    leftTs :: forall b. Code Q ts -> (Code Q ts -> Code Q b) -> Code Q b,
    rightTs :: forall b. Code Q ts -> (Code Q ts -> Code Q b) -> Code Q b,
    nextState ::
      forall a b.
      Code Q ts -> Code Q es -> Code Q (Free (NonDet :+: Void) a) ->
        -- Code Q ((ts -> es -> (Free (NonDet :+: Void) a) -> b) -> b)
        (Code Q ts -> Code Q es -> Code Q (Free (NonDet :+: Void) a) -> Code Q b) -> Code Q b
  }


dbsTrans :: Int -> SearchTransformer Int ()
dbsTrans depthLimit =
  SearchTransformer
    { tsInit = [||0||],
      esInit = [||()||],
      solEs = \esc k -> k esc,
      leftTs = \ts k -> k [|| succ $$ts ||],
      rightTs = \ts k -> k [|| succ $$ts ||],
      -- nextState = \tsc esc model k -> k tsc esc [|| if $$tsc <= depthLimit then $$model else fail ||]
      nextState = \ts es model k -> k ts es [|| if $$ts <= depthLimit then $$model else fail||]
    }

nbsTrans :: Int -> SearchTransformer () Int 
nbsTrans nodeLimit = 
  SearchTransformer
    { tsInit = [|| () ||]
    , esInit = [|| 0 ||]
    , solEs = \esc k -> k esc
    , leftTs = flip ($)
    , rightTs = flip ($)
    , nextState = \ts es model k -> k ts [|| succ $$es ||] [||if $$es <= nodeLimit then $$model else fail||]
    }

ldsTrans :: Int -> SearchTransformer Int ()
ldsTrans discLimit = 
  SearchTransformer
  { tsInit = [|| 0 ||]
  , esInit = [|| () ||]
  , solEs = flip ($)
  , leftTs = flip ($)
  , rightTs = \ts k -> k [|| succ $$ts ||]
  , nextState = \ts es model k -> k ts es [|| if $$ts <= discLimit then $$model else fail ||]
  }

dbsTrans25 :: SearchTransformer Int ()
dbsTrans25 = dbsTrans 25

nbsTrans500000 :: SearchTransformer () Int 
nbsTrans500000 = nbsTrans 500000

ldsTrans5000000 :: SearchTransformer Int ()
ldsTrans5000000 = ldsTrans 5000000

dbsNbsTrans :: SearchTransformer (Int, ()) ((), Int)
dbsNbsTrans = composeTrans dbsTrans25 nbsTrans500000

dbsNbsLdsTrans :: SearchTransformer ((Int, ()), Int) (((), Int), ())
dbsNbsLdsTrans = composeTrans dbsNbsTrans ldsTrans5000000

stagedDbs25 :: Code Q ([(Int, Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
stagedDbs25 = stageOne dbsTrans25 

stagedDbsNbs :: Code Q ([((Int, ()), Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
stagedDbsNbs = stageOne dbsNbsTrans

stagedDbsNbsLds :: Code Q ( [( ((Int, ()), Int) , Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a] )
stagedDbsNbsLds = stageOne dbsNbsLdsTrans

stageOne :: forall q ts es a. (Queue q, Elem q ~ (ts, Free (NonDet :+: Void) a)) =>
  SearchTransformer ts es -> 
  Code Q (q -> Free (NonDet :+: Void) a -> Free Void [a])
stageOne (SearchTransformer tsInit esInit solEs leftTs rightTs nextState) = rec2 
  (\(_, continue) -> codeCurry $ \tsc -> codeCurry $ \esc -> 
    [||
    \q tree -> case tree of 
      Pure a -> $$(solEs' esc $ \esc' -> [|| (a:) <$> $$continue $$esc' q||]) 
      l :|: r -> $$(leftTs' tsc $ \tsL -> rightTs' tsc $ \tsR ->
        [|| $$continue $$esc (pushQ ($$tsL, l) $ pushQ ($$tsR, r) q) ||])
      Fail -> $$continue $$esc q
    ||]
    )
  (\(go, _) -> [||
    \es q -> if nullQ q then pure [] else
      let ((ts, tree),q') = popQ q in
        $$(nextState' [||ts||] [||es||] [||tree||] $ \ts' es' tree' -> [||$$go $$ts' $$es' q' $$tree'||])
  ||])
  (\(go, _) -> [|| $$go $$tsInit $$esInit ||])
  where 
    solEs' = solEs @(Free Void [a]) 
    leftTs' = leftTs @(Free Void [a])
    rightTs' = rightTs @(Free Void [a])
    nextState' = nextState @a @(Free Void [a])

composeTrans :: SearchTransformer ts1 es1 -> SearchTransformer ts2 es2 -> SearchTransformer (ts1, ts2) (es1, es2)
composeTrans t1 t2 =
  SearchTransformer {
    tsInit = [|| ($$(tsInit t1), $$(tsInit t2)) ||]
  , esInit = [|| ($$(esInit t1), $$(esInit t2)) ||] 
  , solEs = \esc k -> let es1 = [|| fst $$esc ||]
                          es2 = [|| snd $$esc ||]
                           in (solEs t1 es1) $ \es1' -> (solEs t2 es2) $ \es2' -> k [|| ($$es1', $$es2') ||]
  , leftTs = \ts k -> let ts1 = [|| fst $$ts ||]
                          ts2 = [|| snd $$ts ||]
                        in (leftTs t1 ts1) $ \ts1' -> (leftTs t2 ts2) $ \ts2' -> k [|| ($$ts1', $$ts2') ||]
  , rightTs = \ts k -> let ts1 = [|| fst $$ts ||]
                           ts2 = [|| snd $$ts ||]
                        in (rightTs t1 ts1) $ \ts1' -> (rightTs t2 ts2) $ \ts2' -> k [|| ($$ts1', $$ts2') ||]
  , nextState = \ts es tree k -> let ts1 = [|| fst $$ts ||]
                                     ts2 = [|| snd $$ts ||]
                                     es1 = [|| fst $$es ||]
                                     es2 = [|| snd $$es ||]
                                  in (nextState t1 ts1 es1 tree) $ \ts1' es1' tree' ->
                                    (nextState t2 ts2 es2 tree') $ \ts2' es2' tree'' -> 
                                      k [|| ($$ts1', $$ts2') ||] [|| ($$es1', $$es2') ||] tree''
}


-- ------------------------------------------


type Mk2 a b c = (Code Q a, Code Q b) -> Code Q c

rec2 :: Mk2 a b a -> Mk2 a b b -> Mk2 a b c -> Code Q c
rec2 mk1 mk2 mkk = [|| let f = $$(mk1 ([|| f ||], [|| g ||]))
                           g = $$(mk2 ([|| f ||], [|| g ||]))
                          in $$(mkk ([|| f ||], [|| g ||])) ||]

isEven :: Code Q (Integer -> Bool)
isEven = rec2
  (\(_     , isOdd) -> [|| \case 0 -> True  ; n -> $$isOdd (n-1) ||])
  (\(isEven, _    ) -> [|| \case 0 -> False ; n -> $$isEven (n-1) ||])
  (\(isEven, _    ) -> isEven)

y :: (Code Q a -> Code Q a) -> Code Q a
y f = [|| let g = $$(f [|| g ||]) in g ||]

add :: Integer -> Code Q (Integer -> Integer)
add a = y (\add -> [|| \n -> if n > 0 then a + $$add (n-1) else 0 ||])
 
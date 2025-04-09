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

module StagedHandlers where

import Control.Monad.Free
import Effects
import Language.Haskell.TH
import qualified Language.Haskell.TH.Syntax
import NonDet
import Queues
import Prelude hiding (fail)
import Data.Bifunctor (Bifunctor(bimap))

codeCurry :: (CodeQ a -> CodeQ b) -> CodeQ (a -> b)
codeCurry f = [||\a -> $$(f [||a||])||]


data SearchTransformer ts es = SearchTransformer
  { tsInit :: Code Q ts,
    esInit :: Code Q es,
    solEs :: Code Q (es -> es),
    leftTs :: Code Q (ts -> ts),
    rightTs :: Code Q (ts -> ts),
    nextState ::
      forall sig a.
      (Functor sig) =>
      Code Q (ts -> es -> Free (NonDet :+: sig) a -> (ts, es, Free (NonDet :+: sig) a))
  }

dbsTrans :: Int -> SearchTransformer Int ()
dbsTrans depthLimit =
  SearchTransformer
    { tsInit = [||0||],
      esInit = [||()||],
      solEs = [||id||],
      leftTs = [||succ||],
      rightTs = [||succ||],
      nextState = [||\depth u tree -> (depth, u, if depth <= depthLimit then tree else fail)||]
    }

nbsTrans :: Int -> SearchTransformer () Int 
nbsTrans nodeLimit = 
  SearchTransformer
    { tsInit = [|| () ||]
    , esInit = [|| 0 ||]
    , solEs = [|| id ||]
    , leftTs = [|| id ||]
    , rightTs = [|| id ||]
    , nextState = [||\u nodes tree -> (u, nodes + 1, if nodes <= nodeLimit then tree else fail) ||]
    }

dbsTrans25 :: SearchTransformer Int ()
dbsTrans25 = dbsTrans 25

nbsTrans500000 :: SearchTransformer () Int 
nbsTrans500000 = nbsTrans 500000

dbsNbsTrans :: SearchTransformer (Int, ()) ((), Int)
dbsNbsTrans = composeTrans dbsTrans25 nbsTrans500000

stagedDbs25 :: Code Q ([(Int, Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
stagedDbs25 = stageOne dbsTrans25 

stagedDbsNbs :: Code Q ([((Int, ()), Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
stagedDbsNbs = stageOne dbsNbsTrans

stageOne :: forall q ts es a. (Queue q, Elem q ~ (ts, Free (NonDet :+: Void) a)
  , Language.Haskell.TH.Syntax.Lift ts
  , Language.Haskell.TH.Syntax.Lift es ) =>
  SearchTransformer ts es -> 
  Code Q (q -> Free (NonDet :+: Void) a -> Free Void [a])
stageOne (SearchTransformer tsInit esInit solEs leftTs rightTs nextState) = rec2 
  (\(_, continue) -> [||
  \ts es q model -> 
    case model of 
      Pure a  -> (a:) <$> $$continue ($$solEs es) q
      l :|: r -> let q' = pushQ ($$leftTs ts , l) $ pushQ ($$rightTs ts, r) q in $$continue es q'
      Fail    -> $$continue es q
  ||])
  (\(go, _) -> [||
  \es q -> if nullQ q then pure [] else
    let ((ts, tree),q') = popQ q 
        (ts', es', tree') = $$nextState ts es tree 
    in $$go ts' es' q' tree'
  ||])
  (\(go, _) -> [|| $$go $$tsInit $$esInit ||])


composeTrans :: SearchTransformer ts1 es1 -> SearchTransformer ts2 es2 -> SearchTransformer (ts1, ts2) (es1, es2)
composeTrans t1 t2 = SearchTransformer {
  tsInit    = [|| ($$(tsInit t1), $$(tsInit t2)) ||],
  esInit    = [|| ($$(esInit t1), $$(esInit t2)) ||],
  solEs     = [|| bimap $$(solEs t1) $$(solEs t2) ||],
  leftTs    = [|| bimap $$(leftTs t1) $$(leftTs t2) ||],
  rightTs   = [|| bimap $$(rightTs t1) $$(rightTs t2) ||],
  nextState = [|| \(ts1, ts2) (es1, es2) tree -> let (ts1', es1', tree') = $$(nextState t1) ts1 es1 tree
                                                     (ts2', es2', tree'') = $$(nextState t2) ts2 es2 tree' 
                                                     in
                                                      ((ts1',ts2'), (es1', es2'), tree'') ||]
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

yBad :: (Code Q a -> Code Q a) -> Code Q a 
yBad f = f [|| $$(yBad f) ||] -- = f (yBad f)

add :: Integer -> Code Q (Integer -> Integer)
add a = y (\add -> [|| \n -> if n > 0 then a + $$add (n-1) else 0 ||])
 
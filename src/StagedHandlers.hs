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

dbsTrans25 :: SearchTransformer Int ()
dbsTrans25 = dbsTrans 25

makeContinue :: forall q ts es a. (Queue q, Elem q ~ (ts, Free (NonDet :+: Void) a)
  , Language.Haskell.TH.Syntax.Lift ts
  , Language.Haskell.TH.Syntax.Lift es) =>
  SearchTransformer ts es -> 
  Code Q (ts -> es -> q -> Free (NonDet :+: Void) a -> Free Void [a]) ->
  Code Q (q -> es -> Free Void [a])
makeContinue (SearchTransformer _ _ _ _ _ nextState) traverse = go 
  where 
    go :: Code Q (q -> es -> Free Void [a])
    go = [|| \q es -> 
      if nullQ q then pure [] else (
        let ((ts,tree), q') = popQ q in
        let (ts', es', tree') = $$nextState ts es tree in 
          $$traverse ts' es' q' tree'
      ) ||]

makeTraverse :: forall q ts es a. (Queue q, Elem q ~ (ts, Free (NonDet :+: Void) a)
  , Language.Haskell.TH.Syntax.Lift ts
  , Language.Haskell.TH.Syntax.Lift es) =>
  SearchTransformer ts es -> 
  Code Q (q -> es -> Free Void [a]) ->
  Code Q (ts -> es -> q -> Free (NonDet :+: Void) a -> Free Void [a])
makeTraverse (SearchTransformer _ _ solEs leftTs rightTs _) continue = go 
  where 
    go :: Code Q (ts -> es -> q -> Free (NonDet :+: Void) a -> Free Void [a])
    go = [|| 
      \ts es q model -> case model of 
        Pure a -> (a :) <$> $$continue q ($$solEs es)
        l :|: r -> let q' = pushQ ($$leftTs ts, l) $ pushQ ($$rightTs ts, r) q
                    in $$continue q' es
        Fail -> $$continue q es
       ||]

stageOne' :: forall q ts es a. (Queue q, Elem q ~ (ts, Free (NonDet :+: Void) a)
  , Language.Haskell.TH.Syntax.Lift ts
  , Language.Haskell.TH.Syntax.Lift es ) =>
  SearchTransformer ts es -> 
  Code Q (Free (NonDet :+: Void) a -> Free Void [a])
stageOne' transformer = [||\model -> $$traverse $$(tsInit transformer) $$(esInit transformer) emptyQ model||] 
  where 
    traverse :: Code Q (ts -> es -> q -> Free (NonDet :+: Void) a -> Free Void [a])
    traverse = makeTraverse transformer [|| \q es -> $$continue q es ||]
    continue :: Code Q (q -> es -> Free Void [a])
    continue = makeContinue transformer [|| \ts es q tree -> $$traverse ts es q tree ||]

stagedDbs25 :: forall a. Code Q (Free (NonDet :+: Void) a -> Free Void [a])
stagedDbs25 = stageOne @[(Int, Free (NonDet :+: Void) a)] @Int @() @a dbsTrans25 


stageOne :: forall q ts es a. (Queue q, Elem q ~ (ts, Free (NonDet :+: Void) a)
  , Language.Haskell.TH.Syntax.Lift ts
  , Language.Haskell.TH.Syntax.Lift es ) =>
  SearchTransformer ts es -> 
  Code Q (Free (NonDet :+: Void) a -> Free Void [a])
stageOne (SearchTransformer tsInit esInit solEs leftTs rightTs nextState) = undefined
  -- [|| $$goiv $$tsInit $$esInit emptyQ ||]
  where
    go' :: Code Q (ts -> es -> q -> Free (NonDet :+: Void) a -> Free Void [a])
    -- go' = codeCurry $ \tsc -> codeCurry $ \esc -> codeCurry $ \qc -> codeCurry $ go tsc esc qc
    go' = [|| 
      \ts es q model -> 
        case model of 
          Pure a -> (a:) <$> $$continue' q ($$solEs es)
          l :|: r -> let q' = pushQ ($$leftTs ts, l) $ pushQ ($$rightTs ts, r) q
            in $$continue' q' es
          Fail -> $$continue' q es 
      ||]


    go'' :: (Code Q ts -> Code Q es -> Code Q q -> Code Q (Free (NonDet :+: Void) a) -> Code Q (Free Void [a])) ->
      (Code Q ts -> Code Q es -> Code Q q -> Code Q (Free (NonDet :+: Void) a) -> Code Q (Free Void [a]))
    go'' next ts es q model = 
      let continue = [||
            \q es -> if nullQ q then pure [] else (
              let ((ts, tree), q') = popQ q in 
                let (ts', es', tree') = $$nextState ts es tree in 
                  $$(next [||ts'||] [||es'||] [||q'||] [||tree'||])
            )
            ||]
      in [|| 
      case $$model of
        Pure a -> (a:) <$> $$continue $$q ($$solEs $$es)

        l :|: r -> let q' = pushQ ($$leftTs $$ts, l) $ pushQ ($$rightTs $$ts, r) $$q

          in $$continue q' $$es
        Fail -> $$continue $$q $$es
      ||]
      

    -- go :: Code Q ts -> Code Q es -> Code Q q -> Code Q (Free (NonDet :+: Void) a) -> Code Q (Free Void [a])
    -- go ts es q model = [||
    --   case $$model of
    --     Pure a -> (a:) <$> $$(continue q [||$$solEs $$es||])
    --     l :|: r -> let q' = pushQ ($$leftTs $$ts, l) $ pushQ ($$rightTs $$ts, r) $$q
    --       in $$(continue [||q'||] es)
    --     Fail -> $$(continue q es)
    --   ||]

    -- continue :: Code Q q -> Code Q es -> Code Q (Free Void [a])
    -- continue q es = [||
    --       if nullQ $$q then pure [] else (
    --         let ((ts, tree), q') = popQ $$q in
    --         let (ts', es', tree') = $$nextState ts $$es tree in
    --           $$(go') ts' es' q' tree'
    --       )
    --   ||]

    continue' :: Code Q (q -> es -> Free Void [a])
    continue' = [|| 
      \q es -> 
        if nullQ q then pure [] else (
          let ((ts, tree), q') = popQ q in 
            let (ts', es', tree') = $$nextState ts es tree in 
              $$go' ts' es' q' tree'
        ) 
      ||]

-- ------------------------------------------

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
 
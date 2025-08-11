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
module Staging.IncrementalOptimisation5 where
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

let_ :: Rep (a, b) -> ContRep (Rep a, Rep b)
let_ (Pair l r) = pure (l, r)
let_ (Dyn p) = R $ \k -> Dyn [|| let (a, b) = $$p in $$(dynP (curry k (Dyn [||a||]) (Dyn [||b||]))) ||]

pairP :: Rep a -> Rep b -> Rep (a, b)
pairP = Pair

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

data StateTransform state = 
  IdState 
  | TransState (Rep state -> ContRep (Rep state))

data StateTransform2 state = 
  IdState2
  | TransState2 (Rep state -> ContRep (Rep state, Rep state))

getCont :: StateTransform state -> Rep state -> ContRep (Rep state)
getCont IdState = pure 
getCont (TransState f) = f

getCont2 :: StateTransform2 state -> Rep state -> ContRep (Rep state, Rep state)
getCont2 IdState2 = pure . (\a -> (a,a))
getCont2 (TransState2 f) = f

mkTrans :: (Rep state -> Rep state) -> StateTransform state 
mkTrans f = TransState $ \s -> pure (f s)

mkTrans2 :: (Rep state -> Rep state) -> StateTransform2 state 
mkTrans2 f = TransState2 $ \s -> pure (f s, s)

newtype NextTransform ts es
  = NT ( forall a.
        Rep ts -> Rep es ->
        Rep (Free (NonDet :+: Void) a) ->
        ContRep ( Maybe (Rep ts), Maybe (Rep es),
          Rep (Free (NonDet :+: Void) a)
        ))

getNextTransform ::
  NextTransform ts es ->
  Rep ts ->
  Rep es ->
  Rep (Free (NonDet :+: Void) a) ->
  ContRep (Rep ts, Rep es, Rep (Free (NonDet :+: Void) a))
getNextTransform (NT f) = \ts es tree -> do
  -- let (ts', es', tree') = (r f) ts es tree
  --  in ( maybe ts id ts',
  --       maybe es id es',
  --       tree'
  --     )
  (ts', es', tree') <- f ts es tree 
  pure (maybe ts id ts', maybe es id es', tree')


noneT :: (forall a. Rep ts -> Rep es -> (Rep (Free (NonDet :+: Void) a)) -> (Rep (Free (NonDet :+: Void) a))) -> 
    NextTransform ts es
noneT f = NT $ \ts es tree -> pure (Nothing, Nothing, f ts es tree)

onlyEsT :: (forall a. Rep ts -> Rep es -> (Rep (Free (NonDet :+: Void) a)) -> (Rep es, (Rep (Free (NonDet :+: Void) a)))) -> 
  NextTransform ts es
onlyEsT f = NT $ \ts es tree -> let (es', tree') = f ts es tree in pure (Nothing, Just es', tree')

data SearchTransformer ts es = SearchTransformer 
  { tsInit :: Rep ts,
    esInit :: Rep es,
    leftTs :: StateTransform2 ts,
    rightTs :: StateTransform ts,
    nextState :: NextTransform ts es
  }

dbsTrans' :: Int -> SearchTransformer Int () 
dbsTrans' depthLimit = SearchTransformer 
  { tsInit = Dyn [|| 0 ||]
  , esInit = Dyn [|| () ||]
  , leftTs = mkTrans2 $ \ts -> Dyn [|| $$(dynP ts) + 1 ||]
  , rightTs = mkTrans $ \ts -> Dyn [|| $$(dynP ts) + 1 ||]
  , nextState = noneT $ \ts _ tree -> Dyn [|| if $$(dynP ts) <= depthLimit then $$(dynP tree) else fail ||]
  }

nbsTrans' :: Int -> SearchTransformer () Int 
nbsTrans' nodeLimit = 
  SearchTransformer
    { tsInit = Dyn [|| () ||]
    , esInit = Dyn [|| 0 ||]
    , leftTs = IdState2
    , rightTs = IdState
    , nextState = onlyEsT $ \_ es tree -> 
      (Dyn [|| $$(dynP es) + 1 ||], Dyn [|| if $$(dynP es) <= nodeLimit then $$(dynP tree) else fail ||])
    }

randTrans' :: Int -> SearchTransformer () [Bool]
randTrans' seed = SearchTransformer 
  { tsInit = Dyn [|| () ||]
  , esInit = Dyn [|| randoms $ mkStdGen seed ||]
  , leftTs = IdState2
  , rightTs = IdState 
  , nextState = onlyEsT $ \_ es tree -> (Dyn [|| tail $$(dynP es) ||], 
    Dyn [|| let tree' = $$(dynP tree) in if head $$(dynP es) then flipT tree' else tree' ||])
  }

pairMaybe :: Rep a -> Rep b -> Maybe (Rep a) -> Maybe (Rep b) -> Maybe (Rep (a, b))
pairMaybe defA defB a b = case (a,b) of 
  (Nothing, Nothing) -> Nothing 
  (a, b) -> Just $ pairP (maybe defA id a) (maybe defB id b)

composeTrans' :: SearchTransformer ts1 es1 -> 
  SearchTransformer ts2 es2 -> 
  SearchTransformer (ts1, ts2) (es1, es2)
composeTrans' t1 t2 = SearchTransformer 
  { tsInit = pairP (tsInit t1) (tsInit t2)
  , esInit = pairP (esInit t1) (esInit t2) 
  , leftTs = case (leftTs t1, leftTs t2) of 
      (IdState2, IdState2) -> IdState2 
      (f1, f2) -> TransState2 $ \ts -> do 
        (tsL, tsR) <- let_ ts 
        (tsL', tsL0) <- getCont2 f1 $ tsL 
        (tsR', tsR0) <- getCont2 f2 $ tsR 
        pure $ (pairP tsL' tsR', pairP tsL0 tsR0)
  , rightTs = case (rightTs t1, rightTs t2) of 
      (IdState, IdState) -> IdState 
      (f1, f2) -> TransState $ \ts -> do 
        (tsL, tsR) <- let_ ts 
        tsL' <- getCont f1 $ tsL 
        tsR' <- getCont f2 $ tsR 
        pure $ pairP tsL' tsR'
  , nextState = let 
        (NT f1) = nextState t1 
        (NT f2) = nextState t2 in NT $ \tsP esP tree -> do 
          (tsL, tsR) <- let_ tsP 
          (esL, esR) <- let_ esP 
          (tsL', esL', tree') <- f1 tsL esL tree
          (tsR', esR', tree'') <- f2 tsR esR tree' 
          pure $ (pairMaybe tsL tsR tsL' tsR', pairMaybe esL esR esL' esR', tree'')
}

stage' :: forall q ts es a. (Queue q, Elem q ~ (ts, Free (NonDet :+: Void) a)) =>
  SearchTransformer ts es -> 
  Code Q (q -> Free (NonDet :+: Void) a -> Free Void [a])
stage' (SearchTransformer tsInit esInit leftTs rightTs nextState) = rec2 
  (\(_, continue) ->  
    [||
    \ts es q tree -> case tree of 
      Pure a -> (a:) <$> $$continue es q
      l :|: ri -> $$(dynP $ (r $ getCont2 leftTs (Dyn [|| ts ||])) $ \(tsL, ts0) -> (r $ getCont rightTs ts0) $ \tsR -> 
        Dyn [|| $$continue es (pushQ ($$(dynP tsL), l) $ pushQ ($$(dynP tsR), ri) q)||])
      Fail -> $$continue es q
    ||]
    )
  (\(go, _) -> [||
    \es q -> if nullQ q then pure [] else
      let ((ts, tree),q') = popQ q in
        $$(dynP $ 
          r ( getNextTransform nextState (Dyn [||ts||]) (Dyn [||es||]) (Dyn [||tree||]) ) $ 
          \(ts', es', tree') -> Dyn [|| $$go $$(dynP ts') $$(dynP es') q' $$(dynP tree') ||]
          )
  ||])
  (\(go, _) -> [|| $$go $$(dynP tsInit) $$(dynP esInit) ||])

exampleTrans :: SearchTransformer ((Int, ()), ()) (((), [Bool]), Int)
exampleTrans = composeTrans' (composeTrans' (dbsTrans' 15) (randTrans' 300)) (nbsTrans' 1500)

stagedExample :: Code Q ([(((Int, ()), ()), Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
stagedExample = stage' exampleTrans

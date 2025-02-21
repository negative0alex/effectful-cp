{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Transformer(TransformerE(..), leftT, rightT, nextT, pattern LeftT, pattern RightT, pattern NextT, pattern InitT, initT, pattern SolT, solT) where 
import Control.Monad.Free
import Effects

data TransformerE ts es el cnt where 
  LeftT'  :: ts -> (ts -> cnt) -> TransformerE ts es el cnt 
  RightT' :: ts -> (ts -> cnt) -> TransformerE ts es el cnt   
  NextT'  :: el -> ts -> es -> (el -> ts -> es -> cnt) -> TransformerE ts es el cnt
  InitT'  :: (ts -> es -> cnt) -> TransformerE ts es el cnt
  SolT'   :: es -> (es -> cnt) -> TransformerE ts es el cnt
  
 
instance Functor (TransformerE ts es el) where 
  fmap :: (a -> b) -> TransformerE ts es el a -> TransformerE ts es el b
  fmap f (LeftT' ts k)  = LeftT' ts (f.k)
  fmap f (RightT' ts k) = RightT' ts (f.k)
  -- fmap f (NextT' ss)    = NextT' (\e q ts es -> f <$> ss e q ts es)
  fmap f (NextT' el ts es cnt) = NextT' el ts es (\el' ts' es' -> f $ cnt el' ts' es')
  fmap f (InitT' k) = InitT' ((\ts es  -> f $ k ts es))
  fmap f (SolT' es k) = SolT' es (f.k)

pattern LeftT :: forall ts es sig cnt el. (Functor sig) =>
  ts -> (ts -> Free (TransformerE ts es el :+: sig) cnt) -> Free (TransformerE ts es el :+: sig)  cnt 
pattern LeftT ts k <- (getL -> Just (LeftT' ts k))

-- pattern LeftT :: forall ts es el sig cnt. 
--   (TransformerE ts es el `Sub` sig) => ts -> (ts -> Free sig cnt) -> Free sig cnt 
-- pattern LeftT ts k <- (project @(TransformerE ts es el) @sig -> Just (LeftT' ts k))

leftT :: forall ts es sig cnt el. (Functor sig) =>
  ts -> (ts -> Free (TransformerE ts es el :+: sig) cnt) -> Free (TransformerE ts es el :+: sig) cnt 
leftT ts k = putL (LeftT' ts k)


pattern RightT :: forall ts es sig cnt el. (Functor sig) =>
  ts -> (ts -> Free (TransformerE ts es el :+: sig) cnt) -> Free (TransformerE ts es el :+: sig)  cnt 
pattern RightT ts k <- (getL -> Just (RightT' ts k))

rightT :: forall ts es sig cnt el. (Functor sig) =>
  ts -> (ts -> Free (TransformerE ts es el :+: sig) cnt) -> Free (TransformerE ts es el :+: sig) cnt 
rightT ts k = putL (RightT' ts k)


pattern NextT :: forall ts es sig cnt el. (Functor sig) =>
  el -> ts -> es -> (el -> ts -> es -> Free (TransformerE ts es el :+: sig) cnt) -> Free (TransformerE ts es el :+: sig) cnt 
pattern NextT el ts es k <- (getL -> Just (NextT' el ts es k))

nextT :: forall ts es sig cnt el. (Functor sig) =>
  el -> ts -> es -> (el -> ts -> es -> Free (TransformerE ts es el :+: sig) cnt) -> Free (TransformerE ts es el :+: sig) cnt 
nextT el ts es k = putL (NextT' el ts es k)

pattern InitT :: forall ts es sig cnt el. (Functor sig) =>
  (ts -> es -> Free (TransformerE ts es el :+: sig) cnt) -> Free (TransformerE ts es el :+: sig) cnt 
pattern InitT k <- (getL -> Just (InitT' k))

initT :: forall ts es sig cnt el. (Functor sig) =>
  (ts -> es -> Free (TransformerE ts es el :+: sig) cnt) -> Free (TransformerE ts es el :+: sig) cnt 
initT k = putL (InitT' k)

pattern SolT :: forall ts es sig cnt el. (Functor sig) => 
  es -> (es -> Free (TransformerE ts es el :+: sig) cnt) -> Free (TransformerE ts es el :+: sig) cnt 
pattern SolT es k <- (getL -> (Just (SolT' es k)))

solT :: forall ts es sig cnt el. (Functor sig) => 
  es -> (es -> Free (TransformerE ts es el :+: sig) cnt) -> Free (TransformerE ts es el :+: sig) cnt 
solT es k = putL (SolT' es k)

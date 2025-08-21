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
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
module Effects.Transformer(TransformerE(..), leftT, rightT, nextT, pattern LeftT, pattern RightT, pattern NextT, pattern InitT, initT, pattern SolT, solT, leftS, rightS) where 
import Control.Monad.Free
import Effects.Core

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
  fmap f (NextT' el ts es cnt) = NextT' el ts es (\el' ts' es' -> f $ cnt el' ts' es')
  fmap f (InitT' k) = InitT' ((\ts es  -> f $ k ts es))
  fmap f (SolT' es k) = SolT' es (f.k)

pattern LeftT ts k <- (project -> Just (LeftT' ts k))

leftT :: forall ts es el a sig. (TransformerE ts es el `Sub` sig) => ts -> (ts -> Free sig a) -> Free sig a
leftT ts k = inject (LeftT' @ts @(Free sig a) @es @el ts k)

leftS ts = leftT ts pure

pattern RightT ts k <- (project -> Just (RightT' ts k))

rightT :: forall ts es el a sig. (TransformerE ts es el `Sub` sig) => ts -> (ts -> Free sig a) -> Free sig a
rightT ts k = inject (RightT' @ts @(Free sig a) @es @el ts k)

rightS ts = rightT ts pure

pattern NextT el ts es k <- (project -> Just (NextT' el ts es k))

nextT :: (TransformerE ts es el) `Sub` sig => el -> ts -> es -> (el -> ts -> es -> Free sig a) -> Free sig a
nextT el ts es k = inject (NextT' el ts es k)

pattern InitT k <- (project -> Just (InitT' k))

initT :: forall ts es el a sig. (TransformerE ts es el `Sub` sig) => (ts -> es -> Free sig a) -> Free sig a
initT k = inject (InitT' @ts @es @(Free sig a) @el k)

pattern SolT es k <- (project -> (Just (SolT' es k)))

solT:: forall ts es el a sig. (TransformerE ts es el `Sub` sig) => es -> (es -> Free sig a) -> Free sig a
solT es k = inject (SolT' @es @(Free sig a) @ts @el es k)
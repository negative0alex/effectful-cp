{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
module Effects.Algebra where
import Control.Monad.Free (Free(..))
import Effects.Core ((:+:) (..))

handle :: Functor f => (f b -> b) -> (a -> b) -> Free f a -> b
handle _alg gen (Pure x)  = gen x 
handle  alg gen (Free op) = alg ((handle alg gen) <$> op) 

handlePara :: Functor f => (Free f a -> f b -> b) -> (a -> b) -> Free f a -> b
handlePara _alg gen (Pure x) = gen x 
handlePara alg gen (Free op) = alg (Free op) (handlePara alg gen <$> op)

-- hdl :: forall g a. Free (F :+: g) a -> H1 (Free g (G1 a))

(<|) :: (f b -> b) -> (g b -> b) -> ((f :+: g) b -> b)
(<|) algF _algG (Inl s) = algF s 
(<|) _algF algG (Inr s) = algG s
infixr 6 <|

(<||) :: (Free h a -> f b -> b) -> (Free h a -> g b -> b) -> (Free h a -> (f :+: g) b -> b)
(<||) algF _algG tree (Inl s) = algF tree s
(<||) _algF algG tree (Inr s) = algG tree s
infixr 6 <||

liftPara :: (b -> c) -> (a -> b -> c)
liftPara f _ = f

-- type Sigma = NonDet :+: State Int :+: Void -- global state 
-- type SigmaLocal = State Int :+: NonDet :+: Void -- local state




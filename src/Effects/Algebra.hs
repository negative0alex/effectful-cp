{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
module Effects.Algebra where
import Control.Monad.Free (Free(..))
import Effects.Core ((:+:) (..), getLUnsafe, getRUnsafe)

handle :: Functor f => (f b -> b) -> (a -> b) -> Free f a -> b
handle _alg gen (Pure x)  = gen x 
handle  alg gen (Free op) = alg $ (handle alg gen) <$> op

handlePara :: Functor f => (f (Free f a, b) -> b) -> (a -> b) -> Free f a -> b
handlePara _alg gen (Pure x) = gen x 
handlePara alg gen (Free op) = alg $ (\fa -> (fa, handlePara alg gen fa)) <$> op

(<|) :: (f b -> b) -> (g b -> b) -> ((f :+: g) b -> b)
(<|) algF _algG (Inl s) = algF s 
(<|) _algF algG (Inr s) = algG s
infixr 6 <|

(<||) :: (Functor f, Functor g) => (f (Free h a, b) -> b) -> (g (Free h a, b) -> b) -> ((f :+: g) (Free h a, b) -> b)
(<||) algF _algG (Inl s) = algF s
(<||) _algF algG (Inr s) = algG s
infixr 6 <||

liftPara :: Functor f => (f b -> b) -> (f (c, b) -> b)
liftPara alg = alg . (snd <$>)

-- type Sigma = NonDet :+: State Int :+: Void -- global state 
-- type SigmaLocal = State Int :+: NonDet :+: Void -- local state




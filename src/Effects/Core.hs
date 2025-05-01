{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveFunctor #-}
module Effects.Core (inject, project, runEffects, pattern Other, Sub(..), (:+:)(..), Void, getL, putL, getRUnsafe, unitr, wrapF, wrapFree)
where
import Control.Monad.Free (Free(..), MonadFree (wrap))


data (sig1 :+: sig2) cnt = Inl (sig1 cnt) | Inr (sig2 cnt)
infixr 7 :+:


instance (Functor sig1, Functor sig2) => Functor (sig1 :+: sig2) where
  fmap f (Inl s1) = Inl (fmap f s1)
  fmap f (Inr s2) = Inr (fmap f s2)


class (Functor sub, Functor sup) => sub `Sub` sup where
  inj  :: sub a -> sup a
  prj :: sup a -> Maybe (sub a)




instance Functor sig => sig `Sub` sig where
  inj = id
  prj = Just


instance  {-# OVERLAPS #-}
  (Functor sig1, Functor sig2) => sig1 `Sub` (sig1 :+: sig2) where
  inj          = Inl
  prj (Inl fa) = Just fa
  prj _        = Nothing

instance {-# INCOHERENT #-}
  (Functor (f a), Functor sig2, a ~ b) => f b `Sub` (f a :+: sig2) where 
    inj = Inl 
    prj (Inl fa) = Just fa
    prj _ = Nothing

instance {-# INCOHERENT #-}
  (Functor (f a b c), Functor sig2, a ~ x, b ~ y, c ~ z) => f x y z `Sub` (f a b c :+: sig2) where 
    inj = Inl 
    prj (Inl fa) = Just fa
    prj _ = Nothing



instance {-# OVERLAPPABLE #-}
  (Functor sig1, sig `Sub` sig2) => sig `Sub` (sig1 :+: sig2) where
  inj          = Inr . inj
  prj (Inr ga) = prj ga
  prj _        = Nothing


inject :: (sub `Sub` sup) => sub (Free sup a) -> Free sup a
inject = Free . inj

project :: (sub `Sub` sup) => Free sup a -> Maybe (sub (Free sup a))
project (Free s) = prj s
project _ = Nothing

getL :: Free (sig1 :+: sig2) a -> Maybe(sig1 (Free (sig1 :+: sig2) a))
getL (Free (Inl a)) = Just a 
getL _ = Nothing

putL :: sig1 (Free (sig1 :+: sig2) a) -> Free (sig1 :+: sig2) a
putL = Free . Inl

getRUnsafe :: (sig1 :+: sig2) a -> sig2 a 
getRUnsafe (Inr a) = a 

getLUnsafe :: (sig1 :+: sig2) a -> sig1 a 
getLUnsafe (Inl a) = a 


data Void cnt deriving Functor

runEffects :: Free Void a -> a
runEffects (Pure x) = x
runEffects _ = error "impossible???"

unitr :: Functor sig => Free (sig :+: Void) a -> Free sig a 
unitr (Pure a) = pure a 
unitr (Free sig) = wrap $ unitr <$> getLUnsafe sig

wrapF :: m `Sub` sig => m a -> Free sig a 
wrapF m = wrap . inj $ pure <$> m

wrapFree :: forall sub sup a. sub `Sub` sup => sub (Free sup a) -> Free sup a 
wrapFree msig = wrap $ inj @sub @sup msig

pattern Other :: sig2 (Free (sig1 :+: sig2) a) -> Free (sig1 :+: sig2) a
pattern Other s = Free (Inr s)


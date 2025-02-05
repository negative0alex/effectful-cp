{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
module SplitCPEffects (inject, project, SplitCPEffects.run, pattern Other, Sub(..), (:+:)(..), Void)
where
import Control.Monad.Free (Free(..))


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

data Void cnt deriving Functor

run :: Free Void a -> a
run (Pure x) = x
run _ = error "impossible???"

pattern Other :: sig2 (Free (sig1 :+: sig2) a) -> Free (sig1 :+: sig2) a
pattern Other s = Free (Inr s)


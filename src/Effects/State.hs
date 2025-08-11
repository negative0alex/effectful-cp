{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Effects.State where
import Control.Monad.Free (Free(..))
import Effects.Core (Sub, project, inject, (:+:), pattern Other)

data State s a where 
  Get' :: (s -> a) -> State s a 
  Put' :: s -> a -> State s a 
  deriving Functor

pattern Get k <- (project -> Just (Get' k))
get :: (State s `Sub` sig) => Free sig s 
get = inject (Get' pure)

pattern Put s k<- (project -> Just (Put' s k))
put :: (State s `Sub` sig) => s -> Free sig ()
put s = inject (Put' s (pure ()))

runState :: Functor sig => s -> Free (State s :+: sig) a -> Free sig (s, a)
runState s (Pure a) = pure (s, a)
runState s (Get k) = runState s (k s) 
runState _ (Put s' k) = runState s' k 
runState s (Other op) = Free (runState s <$> op)

runState' :: s -> Free (State s) a -> (s,a)
runState' s (Pure a) = (s, a)
runState' s (Get k) = runState' s (k s)
runState' _ (Put s' k) = runState' s' k

program :: (State Int `Sub` sig) => Free sig Int 
program = do 
  v <- get
  put (3 * v) 
  pure v

program' :: Free (State Int) Int 
program' = do 
  v <- get 
  put (3 * v)
  pure v

data Free' sig a = 
    Pure' a 
  | Free' (sig (Free' sig a))

instance (Functor sig) => Functor (Free' sig) where 
  fmap :: Functor sig => (a -> b) -> Free' sig a -> Free' sig b
  fmap f (Pure' a) = Pure' (f a)
  fmap f (Free' op) = Free' ((f <$>) <$> op)

instance (Functor sig) => Applicative (Free' sig) where 
  pure = Pure'
  (<*>) (Pure' f) t = f <$> t
  (<*>) (Free' op) t = Free' $ (<*> t) <$> op

instance (Functor sig) => Monad (Free' sig) where 
  (Pure' a) >>= k = k a 
  (Free' op) >>= k = Free' $ (>>= k) <$> op


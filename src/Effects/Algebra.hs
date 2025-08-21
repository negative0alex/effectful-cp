{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
module Effects.Algebra where
import Control.Monad.Free (Free(..))
import Effects.Core (Sub, (:+:) (..), Void)
import Effects.NonDet
import Effects.State
import Effects.Writer

handle :: Functor f => (f b -> b) -> (a -> b) -> Free f a -> b
handle _alg gen (Pure x)  = gen x 
handle  alg gen (Free op) = alg ((handle alg gen) <$> op) 

-- hdl :: forall g a. Free (F :+: g) a -> H1 (Free g (G1 a))

(<|) :: (f b -> b) -> (g b -> b) -> ((f :+: g) b -> b)
(<|) algF _algG (Inl s) = algF s 
(<|) _algF algG (Inr s) = algG s
infixr 6 <|

-- examples from Tom's paper on fusion

handleAllSols :: Functor g => Free (NonDet :+: g) a -> Free g [a]
handleAllSols = handle (algAllSols <| Free) genAllSols

genAllSols :: Functor g => a -> Free g [a]
genAllSols a = pure [a]

algAllSols :: Functor g => NonDet (Free g [a]) -> Free g [a]
algAllSols (Try' l r) = do 
  l' <- l 
  r' <- r 
  pure (l' ++ r')
algAllSols (Fail') = pure []

handleState :: Functor g => Free (State s :+: g) a -> (s -> Free g a)
handleState = handle (algState <| conState) genState 

genState :: Functor g => a -> s -> Free g a
genState a _ = pure a

conState :: Functor g => g (s -> Free g a) -> s -> Free g a
conState op s = Free $ ($ s) <$> op

algState :: Functor g => State s (s -> Free g a) -> s -> Free g a
algState (Get' k) s = k s s
algState (Put' s' k) _ = k s'

handleVoid :: Free Void a -> a 
handleVoid = handle undefined id

type Sigma = NonDet :+: State Int :+: Void -- global state 
type SigmaLocal = State Int :+: NonDet :+: Void -- local state

runSigma :: Free Sigma a -> Int -> [a]
runSigma prog = handleVoid . (handleState . handleAllSols) prog

mySigmaProgram :: Free Sigma Int
mySigmaProgram = try l l
  where 
    l = do 
      v <- get 
      put $ v + 1 
      pure v  

handleLogState :: Free (State s) a -> s -> Free (Writer String :+: Void) a
handleLogState = handle algLogState genState

algLogState ::  (Writer String `Sub` g) => State s (s -> Free g a) -> s -> Free g a
algLogState (Put' s' k) s = do 
  tell "put " 
  k s'
algLogState (Get' k) s = do 
  tell "get "
  k s s

handleLogStateComp :: (Writer String `Sub` g) => Free (State s :+: g) a -> s -> Free g a 
handleLogStateComp = handle (algLogState <| conState) genState

handleWriter :: (Functor g, Monoid w) => Free (Writer w :+: g) a -> Free g (w,a) 
handleWriter = handle (algWriter <| Free) genWriter

genWriter :: (Monad m, Monoid w) => a -> m (w, a)
genWriter a = pure (mempty, a)

algWriter :: (Monad m, Monoid w) => Writer w (m (w, a)) -> m (w, a)
algWriter (Tell w k) = k >>= \ (w', x) -> pure (w <> w', x)

myLoggingProgram :: Int -> Free (State Int) Int 
myLoggingProgram n 
  | n <= 0 = get 
  | otherwise = get >>= \s -> put (s + n) >> myLoggingProgram (n - 1)
  
runLogging :: Int -> (String, Int) 
runLogging n = (handleVoid . handleWriter . handleLogState (myLoggingProgram n)) 0


{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
module NonDet where 
import Control.Monad.Free (Free(..))
import SplitCPEffects(Sub, project, inject)
  
data NonDet a where
  Try'  :: a -> a -> NonDet a
  Fail' :: NonDet a
  deriving Functor

pattern Fail :: (NonDet `Sub` sig) => Free sig a
pattern Fail <- (project -> Just Fail')
fail :: (NonDet `Sub` sig) => Free sig a 
fail = inject Fail'

pattern (:|:) :: (NonDet `Sub` sig) => Free sig a -> Free sig a -> Free sig a
pattern p :|: q <- (project -> Just (Try' p q))
(|||) :: (NonDet `Sub` sig) => Free sig a -> Free sig a -> Free sig a 
p ||| q = inject (Try' p q)
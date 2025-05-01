{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
module Effects.NonDet (fail, pattern (:|:), try, NonDet(..), pattern Fail) where 
import Control.Monad.Free (Free(..))
import Effects.Core (Sub, project, inject)
import Prelude hiding (fail)
  
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
try :: (NonDet `Sub` sig) => Free sig a -> Free sig a -> Free sig a 
try p q = inject (Try' p q)


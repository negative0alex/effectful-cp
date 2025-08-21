{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
module Effects.Writer where
import Control.Monad.Free (Free(..))
import Effects.Core (Sub, project, inject)

data Writer w k where 
  Tell :: w -> k -> Writer w k 
  deriving Functor

tell :: forall w sig. (Writer w `Sub` sig) => w -> Free sig ()
tell w = inject (Tell w (pure ()))
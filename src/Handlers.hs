-- {-# LANGUAGE RankNTypes #-}
-- {-# LANGUAGE TypeOperators #-}
-- {-# LANGUAGE PatternSynonyms #-}
-- {-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE ScopedTypeVariables #-}
-- {-# OPTIONS_GHC -Wno-incomplete-patterns #-}
-- {-# LANGUAGE TypeApplications #-}

-- module Handlers where
-- import NonDet (NonDet, pattern Fail, pattern (:|:), fail, try)
-- import SplitCPEffects (Sub, (:+:) (..), pattern Other, Void)
-- import Control.Monad.Free (Free (..))
-- import Control.Monad (liftM2)
-- import Prelude hiding (fail)
-- import Solver (Solver (..))
-- import CPSolve (CPSolve, pattern NewVar, pattern Add, pattern Dynamic)

-- naiveAllSols :: Functor sig => Free (NonDet :+: sig) a -> Free sig [a]
-- naiveAllSols (Pure a)   = pure [a]
-- naiveAllSols Fail       = pure []
-- naiveAllSols (a :|: b)  = liftM2 (<>) (naiveAllSols a) (naiveAllSols b)
-- naiveAllSols (Other op) = Free (fmap naiveAllSols op)

-- knapsack :: Int -> [Int] -> Free (NonDet :+: Void) [Int]
-- knapsack w vs
--   | w < 0  = fail
--   | w == 0 = pure []
--   | w > 0  = do
--     v <- select vs
--     vs' <- knapsack (w-v) vs
--     pure (v:vs')
--   where
--     select = foldr (try . pure) fail


-- eval :: forall solver sig a. (Solver solver, NonDet `Sub` sig) => Free (CPSolve solver :+: sig) a -> solver (Free sig a)
-- eval (Pure a) = pure . pure $ a
-- eval (NewVar (k :: Term solver -> Free (CPSolve solver :+: sig) a)) = do
--   v <- newvar @solver
--   eval (k v)


{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -ddump-splices #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module Staging where
import Language.Haskell.TH
import CPSolve
import Control.Monad (liftM2)
import Control.Monad.Free
import Effects
import Handlers
import NonDet
import Queues
import Solver
import Transformer
import Prelude hiding (fail)
import StagedHandlers (stageOne, dbsTrans25, SearchTransformer (..))
import StagedHandlers

stagedDfsDbs25 :: Free (NonDet :+: Void) a -> Free Void [a]
stagedDfsDbs25 = $$(stagedDbs25) []

stagedDfsDbsNbs :: Free (NonDet :+: Void) a -> Free Void [a]
stagedDfsDbsNbs = $$(stagedDbsNbs) []

stagedDfsDbsNbsLds :: Free (NonDet :+: Void) a -> Free Void [a]
stagedDfsDbsNbsLds = $$(stagedDbsNbsLds) []

testStagedDbs :: (Solver solver) => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testStagedDbs model = run $ runEffects . stagedDfsDbs25 <$> eval model

testStagedDbsNbs :: (Solver solver) => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testStagedDbsNbs model = run $ runEffects . stagedDfsDbsNbs <$> eval model

testStagedDbsNbsLds :: (Solver solver) => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testStagedDbsNbsLds model = run $ runEffects . stagedDfsDbsNbsLds <$> eval model
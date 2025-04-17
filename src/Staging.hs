{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -ddump-splices #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Staging where
import CPSolve
import Control.Monad.Free
import Effects
import Handlers
import NonDet
import Solver
import Prelude hiding (fail)
import StagedHandlers

stagedDfsRand2801 :: forall a. Free (NonDet :+: Void) a -> Free Void [a]
stagedDfsRand2801 = $$(stageOne @[( (), Free (NonDet :+: Void) a )] randTrans2801) []

stagedDfsDbsRand :: forall a. Free (NonDet :+: Void) a -> Free Void [a]
stagedDfsDbsRand = $$(stageOne @[( (Int, ()), Free (NonDet :+: Void) a )] dbsRandTrans) []

stagedDfsDbs25 :: Free (NonDet :+: Void) a -> Free Void [a]
stagedDfsDbs25 = $$(stagedDbs25) []

stagedDfsDbsNbs :: Free (NonDet :+: Void) a -> Free Void [a]
stagedDfsDbsNbs = $$(stagedDbsNbs) []

stagedDfsDbsNbsLds :: Free (NonDet :+: Void) a -> Free Void [a]
stagedDfsDbsNbsLds = $$(stagedDbsNbsLds) []

testStagedRand2801 :: Solver solver => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testStagedRand2801 model = run $ runEffects . stagedDfsRand2801 <$> eval model

testStagedDbsRand :: Solver solver => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testStagedDbsRand model = run $ runEffects . stagedDfsDbsRand <$> eval model

testStagedDbs :: (Solver solver) => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testStagedDbs model = run $ runEffects . stagedDfsDbs25 <$> eval model

testStagedDbsNbs :: (Solver solver) => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testStagedDbsNbs model = run $ runEffects . stagedDfsDbsNbs <$> eval model

testStagedDbsNbsLds :: (Solver solver) => Free (CPSolve solver :+: (NonDet :+: Void)) a -> [a]
testStagedDbsNbsLds model = run $ runEffects . stagedDfsDbsNbsLds <$> eval model
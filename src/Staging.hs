{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

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

aaa = $$(StagedHandlers.add 5)


{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# LANGUAGE TransformListComp #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Queens where 
import Prelude hiding (fail)
import Data.List (tails)
import FD.OvertonFD as OvertonFD
import FD.Domain as Domain
import GHC.Exts (sortWith)
import Effects.Core ((:+:), Void)
import Effects.CPSolve (CPSolve, exist, in_domain, (@\=), (@\==), (@+), (@=), dynamic)
import Control.Monad.Free (Free)
import Effects.NonDet (try, fail, NonDet)

type CSP = Free (CPSolve OvertonFD :+: NonDet :+: Void)

nqueens :: Int -> CSP [Int]
nqueens n = exist n $ \queens -> model queens n /\ enumerate queens /\ assignments queens

model :: [FDVar] -> Int -> CSP ()
model queens n = queens `allin` (1,n) /\ alldifferent queens /\ diagonals queens

allin :: [FDVar] -> (Int, Int) -> CSP ()
allin queens range = conj [q `in_domain` range | q <- queens]

alldifferent :: [FDVar] -> CSP ()
alldifferent queens = conj [qi @\= qj | qi : qjs <- tails queens, qj <- qjs]

diagonals :: [FDVar] -> CSP ()
diagonals queens = conj [ (qi @\== (qj @+ d)) /\ (qj @\== (qi @+ d)) | qi : qjs <- tails queens, (qj, d) <- zip qjs [1..]]
-- enumerate queens values = conj [ enum queen values | queen <- queens]

enum :: FDVar -> [Int] -> CSP ()
enum var values = disj [ var @= value | value <- values ]

(\/) :: CSP a -> CSP a -> CSP a
(\/) = try
infixl 2 \/

(/\) :: CSP a -> CSP b -> CSP b
(/\) = (>>)
infixl 3 /\

false :: CSP a
false = fail

true :: CSP ()
true = pure ()

disj :: [CSP a] -> CSP a
disj = foldl (\/) false

conj :: [CSP ()] -> CSP ()
conj = foldl (/\) true


-- -----------------------| Labelling |------------------------

enumerate vs = dynamic (label firstfail id vs)

label :: ([FDVar] -> OvertonFD [FDVar]) -> ([Int] -> [Int]) ->
  [FDVar] -> OvertonFD (CSP ())
label varsel valsel vs = do
  vs' <- varsel vs
  label' vs'
  where
    label' [] = pure . pure $ ()
    label' (v:vs) = do
      -- d <- valsel $ Domain.elems $ OvertonFD.lookup v
      d <- fd_domain v
      let d' = valsel d
      pure $ enum v d' /\ dynamic (label varsel valsel vs)

firstfail :: [FDVar] -> OvertonFD [FDVar]
firstfail vs = do
  ds <- mapM OvertonFD.lookup vs
  return [v | (d,v) <- zip ds vs, then sortWith by Domain.size d]

middleout :: [a] -> [a]
middleout l = let n = length l `div` 2 in
  interleave (drop n l) (reverse $ take n l)

interleave :: [a] -> [a] -> [a]
interleave [] ys = ys
interleave (x:xs) ys = x:interleave ys xs

-- ----------------------| Assignment |----------------------

assignments :: [FDVar] -> CSP [Int]
assignments = mapM assignment 
assignment q = dynamic $ do 
  d <- fd_domain q
  let v = head d
  pure $ pure v

-- ----------------------| Knapsack |------------------------

knapsack :: Int -> [Int] -> Free (NonDet :+: Void) [Int]
knapsack w vs
  | w < 0  = fail
  | w == 0 = pure []
  | otherwise  = do
    v <- select vs
    vs' <- knapsack (w-v) vs
    pure (v:vs')
  where
    select = foldr (try . pure) fail

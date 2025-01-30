{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# LANGUAGE TransformListComp #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Queens where
import MyLib
import Prelude hiding (fail)
import Data.List (tails)
import FD.OvertonFD as OvertonFD
import FD.Domain as Domain
import GHC.Exts (sortWith)


nqueens n = exist n $ \queens -> model queens n /\ enumerate queens /\ assignments queens

model queens n = queens `allin` (1,n) /\ alldifferent queens /\ diagonals queens

allin queens range = conj [q `in_domain` range | q <- queens]

alldifferent queens = conj [qi @\= qj | qi : qjs <- tails queens, qj <- qjs]

diagonals queens = conj [ (qi @\== (qj @+ d)) /\ (qj @\== (qi @+ d)) | qi : qjs <- tails queens, (qj, d) <- zip qjs [1..]]
-- enumerate queens values = conj [ enum queen values | queen <- queens]

enum var values = disj [ var @= value | value <- values ]

disj = foldl (\/) false

conj = foldl (/\) true

(\/) = try

false = fail

true :: Solver solver => CPModel solver ()
true = pure ()

(/\) :: Solver solver => CPModel solver a -> CPModel solver b -> CPModel solver b
(/\) = (>>)


-- -----------------------| Labelling |------------------------

enumerate vs = dynamic (label firstfail id vs)

label :: ([FDVar] -> OvertonFD [FDVar]) -> ([Int] -> [Int]) ->
  [FDVar] -> OvertonFD (CPModel OvertonFD ())
label varsel valsel vs = do
  vs' <- varsel vs
  label' vs'
  where
    label' :: [FDVar] -> OvertonFD(CPModel OvertonFD ())
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

assignments :: [FDVar] -> CPModel OvertonFD [Int]
assignments = mapM assignment 
assignment q = dynamic $ do 
  d <- fd_domain q
  let v = head d
  pure $ pure v
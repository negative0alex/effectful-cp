{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
module Staging.Optimisation where
import Data.Kind
import Control.Monad.Free
import Effects.Core
import Language.Haskell.TH hiding (Type)
import Effects.NonDet
import Staging.Handlers (rec2, codeCurry)
import Prelude hiding (fail)
import Queues (Queue, Elem, pushQ, nullQ, popQ)

showCode :: Code Q a -> IO ()
showCode code = do expr <- runQ (unTypeCode (code))
                   putStrLn (pprint expr)

data Rep :: Type -> Type where
   Pair :: Rep a -> Rep b -> Rep (a, b)
   Dyn  :: Code Q a -> Rep a   

fstP :: Rep (a, b) -> Rep a
fstP (Pair l _) = l
fstP (Dyn p) = Dyn [|| fst $$p ||]

sndP :: Rep (a, b) -> Rep b
sndP (Pair _ r) = r
sndP (Dyn p) = Dyn [|| snd  $$p ||]

dynP :: Rep a -> Code Q a
dynP (Pair l r) = [|| ($$(dynP l), $$(dynP r)) ||]
dynP (Dyn p) = p

let_ :: Rep (a, b) -> (Rep a -> Rep b -> Rep c) -> Rep c
let_ (Pair l r) k = k l r
let_ (Dyn p) k = Dyn [|| let (a, b) = $$p in $$(dynP (k (Dyn [||a||]) (Dyn [||b||]))) ||]

-- UNIT ELIMINATION

type Pair :: Type -> Type -> Type
type family Pair a b where 
  Pair a () = a
  Pair () b = b  
  Pair a b = (a,b)


data PairCase a b = 
    LeftC (Rep a -> Rep (Pair a b)) (forall c. Rep (Pair a b) -> (Rep a -> Rep c) -> Rep c) (Rep b)
  | RightC (Rep b -> Rep (Pair a b)) (forall c. Rep (Pair a b) -> (Rep b -> Rep c) -> Rep c) (Rep a)
  | BothC (Rep a -> Rep b -> Rep (Pair a b)) 
    (forall c. Rep (Pair a b) -> (Rep a -> Rep b -> Rep c) -> Rep c) 

class Pairable a b where 
  pairCase :: PairCase a b

instance {-# OVERLAPPING #-} Pairable () () where 
  pairCase = LeftC id (flip ($)) (Dyn [|| () ||])
  
instance {-# OVERLAPS #-} Pairable a () where 
  pairCase = LeftC id (flip ($)) (Dyn [|| () ||])

instance {-# OVERLAPS #-} Pairable () b where 
  pairCase = RightC id (flip ($)) (Dyn [|| () ||])


instance {-# OVERLAPPABLE #-} (Pair a b ~ (a,b)) => Pairable a b where 
  pairCase = BothC Pair let_

nextMerge :: PairCase a b -> Rep (Pair a b) -> 
  (Rep a -> Rep b -> (Rep a -> Rep b -> Rep (Pair a b)) -> Rep c) -> Rep c
nextMerge caseS s k = 
  case caseS of 
              LeftC injL projL defaultR -> projL s $ \l -> k l defaultR (\l _ -> injL l)
              RightC injR projR defaultL -> projR s $ \r -> k defaultL r (\_ r -> injR r) 
              BothC injB projB -> projB s $ \l r -> k l r injB

-- IDENTITY ELIMINATION

data StateTransform state = 
  IdState 
  | Cont (forall r. Rep state -> (Rep state -> Rep r) -> Rep r)

( &>< ) :: StateTransform a -> (Rep a -> Rep b, forall c. Rep b -> (Rep a -> Rep c) -> Rep c) -> StateTransform b
IdState &>< _ = IdState
(Cont k) &>< (f,g) = Cont $ \b k' -> g b $ \a -> k a $ \a' -> k' $ f a'

getCont :: StateTransform state -> (forall r. Rep state -> (Rep state -> Rep r) -> Rep r)
getCont (Cont k) = k
getCont IdState = flip ($)

data StateTransform2 state = 
  IdState2
  | Cont2 (forall r. Rep state -> (Rep state -> Rep state -> Rep r) -> Rep r)

(&&><) :: StateTransform2 a -> (Rep a -> Rep b, forall c. Rep b -> (Rep a -> Rep c) -> Rep c) -> StateTransform2 b
IdState2 &&>< _ = IdState2
(Cont2 k) &&>< (f,g) = Cont2 $ \b k' -> g b $ \a -> k a $ \a' a'' -> k' (f a') (f a'')

getCont2 :: StateTransform2 state -> (forall r. Rep state -> (Rep state -> Rep state -> Rep r) -> Rep r) 
getCont2 (Cont2 k) = k
getCont2 IdState2 = \s k -> k s s


data NextTransform ts es = 
    FullT (forall a b. Rep ts -> Rep es -> Rep (Free (NonDet :+: Void) a) ->
        (Rep ts -> Rep es -> Rep (Free (NonDet :+: Void) a) -> Rep b) -> Rep b)
  | OnlyTsT (forall a b. Rep ts -> Rep es -> Rep (Free (NonDet :+: Void) a) ->
        (Rep ts -> Rep (Free (NonDet :+: Void) a) -> Rep b) -> Rep b)
  | OnlyEsT (forall a b. Rep ts -> Rep es -> Rep (Free (NonDet :+: Void) a) ->
        (Rep es -> Rep (Free (NonDet :+: Void) a) -> Rep b) -> Rep b)
  | NoneT (forall a b. Rep ts -> Rep es -> Rep (Free (NonDet :+: Void) a) ->
        (Rep (Free (NonDet :+: Void) a) -> Rep b) -> Rep b)

getNextTransform :: NextTransform ts es -> 
  (forall b. Rep ts -> Rep es -> Rep (Free (NonDet :+: Void) a) ->
        (Rep ts -> Rep es -> Rep (Free (NonDet :+: Void) a) -> Rep b) -> Rep b)
getNextTransform (FullT f)   = f 
getNextTransform (OnlyTsT f) = \ts es tree k' -> f ts es tree (\ts' tree' -> k' ts' es tree')
getNextTransform (OnlyEsT f) = \ts es tree k' -> f ts es tree (\es' tree' -> k' ts es' tree')
getNextTransform (NoneT f)   = \ts es tree k' -> f ts es tree (\tree' -> k' ts es tree')

data SearchTransformer' ts es = SearchTransformer' 
  { tsInit' :: Rep ts,
    esInit' :: Rep es,
    solEs' :: StateTransform es,
    leftTs' :: StateTransform2 ts,
    rightTs' :: StateTransform ts,
    nextState' :: NextTransform ts es
  }

dbsTrans' :: Int -> SearchTransformer' Int () 
dbsTrans' depthLimit = SearchTransformer' 
  { tsInit' = Dyn [||0||] 
  , esInit' = Dyn [||()||] 
  , solEs' = IdState
  , leftTs' = Cont2 $ \ts k -> k (Dyn [|| succ $$(dynP ts) ||]) ts
  , rightTs' = Cont $ \ts k -> k $ Dyn [|| succ $$(dynP ts) ||]
  , nextState' = NoneT $ \ts _ tree k -> k $ Dyn [|| if $$(dynP ts) <= depthLimit then $$(dynP tree) else fail ||]
  }

nbsTrans' :: Int -> SearchTransformer' () Int 
nbsTrans' nodeLimit = 
  SearchTransformer'
    { tsInit' = Dyn [|| () ||]
    , esInit' = Dyn [|| 0 ||]
    , solEs' = IdState
    , leftTs' = IdState2
    , rightTs' = IdState
    , nextState' = OnlyEsT $ \_ es tree k -> k (Dyn [|| succ $$(dynP es) ||]) 
      (Dyn [|| if $$(dynP es) <= nodeLimit then $$(dynP tree) else fail ||]) 
    }

ldsTrans' :: Int -> SearchTransformer' Int ()
ldsTrans' discLimit = 
  SearchTransformer'
    { tsInit' = Dyn [|| 0 ||]
    , esInit' = Dyn [|| () ||] 
    , solEs' = IdState 
    , leftTs' = IdState2
    , rightTs' = Cont $ \ts k -> k $ Dyn [|| succ $$(dynP ts) ||] 
    , nextState' = NoneT $ \ts _ tree k -> k $ Dyn [|| if $$(dynP ts) <= discLimit then $$(dynP tree) else fail ||]
    }

composeTrans'' :: forall ts1 ts2 es1 es2. (Pairable ts1 ts2, Pairable es1 es2) => 
  SearchTransformer' ts1 es1 -> SearchTransformer' ts2 es2 -> SearchTransformer' (Pair ts1 ts2) (Pair es1 es2)
composeTrans'' t1 t2 = 
  let caseT = pairCase @ts1 @ts2 
      caseE = pairCase @es1 @es2
    in 
      SearchTransformer' 
      { tsInit' = case caseT of  
          LeftC injL _ _ -> injL (tsInit' t1)
          RightC injR _ _ -> injR (tsInit' t2)
          BothC injB _ -> injB (tsInit' t1) (tsInit' t2)

      , esInit' = case caseE of 
          LeftC injL _ _ -> injL (esInit' t1)
          RightC injR _ _ -> injR (esInit' t2)
          BothC injB _ -> injB (esInit' t1) (esInit' t2)

      , solEs' = case caseE of 
          LeftC injL projL _ -> (solEs' t1) &>< (injL, projL)
          RightC injR projR _ -> (solEs' t2) &>< (injR, projR)
          BothC injB projB -> case (solEs' t1, solEs' t2) of 
            (IdState, IdState) -> IdState
            (stl, str) -> Cont $ \es k ->
                          let kl = getCont stl 
                              kr = getCont str 
                              esK = projB es
                            in 
                              esK $ \esL esR -> (kl esL) $ \esL' -> (kr esR) $ \esR' -> k (injB esL' esR')

      , leftTs' = case caseT of 
          LeftC injL projL _ -> (leftTs' t1) &&>< (injL, projL)
          RightC injR projR _ -> (leftTs' t2) &&>< (injR, projR)
          BothC injB projB -> case (leftTs' t1, leftTs' t2) of 
            (IdState2, IdState2) -> IdState2
            (stl, str) -> Cont2 $ \ts k ->
                          let kl = getCont2 stl 
                              kr = getCont2 str 
                              tsK = projB ts
                            in 
                              tsK $ \tsL tsR -> (kl tsL) $ \tsL' tsL0 -> (kr tsR) $ \tsR' tsR0 ->
                                k (injB tsL' tsR') (injB tsL0 tsR0)

      , rightTs' = case caseT of 
          LeftC injL projL _ -> (rightTs' t1) &>< (injL, projL)
          RightC injR projR _ -> (rightTs' t2) &>< (injR, projR)
          BothC injB projB -> case (rightTs' t1, rightTs' t2) of 
            (IdState, IdState) -> IdState
            (stl, str) -> Cont $ \ts k ->
                          let kl = getCont stl 
                              kr = getCont str 
                              tsK = projB ts
                            in 
                              tsK $ \tsL tsR -> (kl tsL) $ \tsL' -> (kr tsR) $ \tsR' -> k (injB tsL' tsR')

      , nextState' = case (nextState' t1, nextState' t2) of 
        -- both get identity
        (NoneT f1, NoneT f2) -> NoneT $ 
          \ts es tree k -> 
            let tK = nextMerge caseT ts
                eK = nextMerge caseE es
            in tK $ \tsL tsR _ -> eK $ \esL esR _ ->
              f1 tsL esL tree $ \tree' -> f2 tsR esR tree' $ \tree'' -> k tree''
        -- es gets identity
        (NoneT f1, OnlyTsT f2) -> OnlyTsT $ 
          \ts es tree k -> 
            let tK = nextMerge caseT ts
                eK = nextMerge caseE es
              in tK $ \tsL tsR mergeT -> eK $ \esL esR _ ->
                f1 tsL esL tree $ \tree' -> f2 tsR esR tree' $ \tsR' tree'' -> k (mergeT tsL tsR') tree'' 
        (OnlyTsT f1, NoneT f2) -> OnlyTsT $ 
          \ts es tree k -> 
            let tK = nextMerge caseT ts
                eK = nextMerge caseE es
              in tK $ \tsL tsR mergeT -> eK $ \esL esR _ ->
                f1 tsL esL tree $ \tsL' tree' -> f2 tsR esR tree' $ \tree'' -> k (mergeT tsL' tsR) tree''
        (OnlyTsT f1, OnlyTsT f2) -> OnlyTsT $ 
          \ts es tree k -> 
            let tK = nextMerge caseT ts
                eK = nextMerge caseE es
              in tK $ \tsL tsR mergeT -> eK $ \esL esR _ ->
                f1 tsL esL tree $ \tsL' tree' -> f2 tsR esR tree' $ \tsR' tree'' -> k (mergeT tsL' tsR') tree''
        -- ts gets identity
        (NoneT f1, OnlyEsT f2) -> OnlyEsT $ 
          \ts es tree k -> 
            let tK = nextMerge caseT ts
                eK = nextMerge caseE es
              in tK $ \tsL tsR _ -> eK $ \esL esR mergeE ->
                f1 tsL esL tree $ \tree' -> f2 tsR esR tree' $ \esR' tree'' -> k (mergeE esL esR') tree'' 
        (OnlyEsT f1, NoneT f2) -> OnlyEsT $ 
          \ts es tree k -> 
            let tK = nextMerge caseT ts
                eK = nextMerge caseE es
              in tK $ \tsL tsR _ -> eK $ \esL esR mergeE ->
                f1 tsL esL tree $ \esL' tree' -> f2 tsR esR tree' $ \tree'' -> k (mergeE esL' esR) tree''
        (OnlyEsT f1, OnlyEsT f2) -> OnlyEsT $ 
          \ts es tree k -> 
            let tK = nextMerge caseT ts
                eK = nextMerge caseE es
              in tK $ \tsL tsR _ -> eK $ \esL esR mergeE ->
                f1 tsL esL tree $ \esL' tree' -> f2 tsR esR tree' $ \esR' tree'' -> k (mergeE esL' esR') tree''
        -- neither gets identity
        (f1T, f2T) -> FullT $ \ts es tree k ->
          let f1 = getNextTransform f1T 
              f2 = getNextTransform f2T 
              tK = nextMerge caseT ts
              eK = nextMerge caseE es 
          in tK $ \tsL tsR mergeT -> eK $ \esL esR mergeE ->
            f1 tsL esL tree $ \tsL' esL' tree' -> f2 tsR esR tree' $ \tsR' esR' tree'' ->
            k (mergeT tsL' tsR') (mergeE esL' esR') tree''
      }


stage2 :: forall q ts es a. (Queue q, Elem q ~ (ts, Free (NonDet :+: Void) a)) =>
  SearchTransformer' ts es -> 
  Code Q (q -> Free (NonDet :+: Void) a -> Free Void [a])
stage2 (SearchTransformer' tsInit' esInit' solEs' leftTs' rightTs' nextState') = rec2 
  (\(_, continue) -> codeCurry $ \tsc -> codeCurry $ \esc -> 
    [||
    \q tree -> case tree of 
      Pure a -> $$(dynP $ ((getCont solEs' (Dyn esc)) $ \esc' -> Dyn [|| (a:) <$> $$continue $$(dynP esc') q||])) 
      l :|: r -> $$(dynP $ (getCont2 leftTs' (Dyn tsc)) $ \tsL ts0 -> (getCont rightTs' ts0) $ \tsR ->
        Dyn [|| $$continue $$esc (pushQ ($$(dynP tsL), l) $ pushQ ($$(dynP tsR), r) q) ||])
      Fail -> $$continue $$esc q
    ||]
    )
  (\(go, _) -> [||
    \es q -> if nullQ q then pure [] else
      let ((ts, tree),q') = popQ q in
        $$(dynP $ (getNextTransform nextState' (Dyn [||ts||]) (Dyn [||es||]) (Dyn [||tree||])) $ 
          \ts' es' tree' -> Dyn [||$$go $$(dynP ts') $$(dynP es') q' $$(dynP tree')||])
  ||])
  (\(go, _) -> [|| $$go $$(dynP tsInit') $$(dynP esInit') ||])

nbsTrans500000' :: SearchTransformer' () Int
nbsTrans500000' = nbsTrans' 500000 

nbsTwiceTrans' :: SearchTransformer' () (Int, Int)
nbsTwiceTrans' = composeTrans'' nbsTrans500000' nbsTrans500000'

nbsTwice' :: Code Q ([((), Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
nbsTwice' = stage2 nbsTwiceTrans'

dbsTrans25' :: SearchTransformer' Int () 
dbsTrans25' = dbsTrans' 25

dbsTwiceTrans' :: SearchTransformer' (Int, Int) ()
dbsTwiceTrans' = composeTrans'' dbsTrans25' dbsTrans25' 

dbsTwice' :: Code Q ([((Int, Int), Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
dbsTwice' = stage2 dbsTwiceTrans'

dbsNbsTrans'' :: SearchTransformer' Int Int
dbsNbsTrans'' = composeTrans'' dbsTrans25' nbsTrans500000'

dbsNbs' :: Code Q ([(Int, Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
dbsNbs' = stage2 dbsNbsTrans''

ldsTrans5000000' :: SearchTransformer' Int ()
ldsTrans5000000' = ldsTrans' 5000000

lds' :: Code Q ([(Int, Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
lds' = stage2 ldsTrans5000000'

ldsTwiceTrans' :: SearchTransformer' (Int, Int) ()
ldsTwiceTrans' = composeTrans'' ldsTrans5000000' ldsTrans5000000'

ldsTwice' :: Code Q ([((Int, Int), Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
ldsTwice' = stage2 ldsTwiceTrans'

dbsNbsLdsTrans'' :: SearchTransformer' (Int, Int) Int
dbsNbsLdsTrans'' = composeTrans'' dbsNbsTrans'' ldsTrans5000000'

dbsNbsLds' :: Code Q ([((Int, Int), Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
dbsNbsLds' = stage2 dbsNbsLdsTrans''
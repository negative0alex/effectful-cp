{- 
 - Origin:
 -      Constraint Programming in Haskell 
 -      http://overtond.blogspot.com/2008/07/pre.html
 -      author: David Overton, Melbourne Australia
 -
 - Modifications:
 -      Monadic Constraint Programming
 -      http://www.cs.kuleuven.be/~toms/Haskell/
 -      Tom Schrijvers
 -}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# HLINT ignore "Use camelCase" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# HLINT ignore "Redundant if" #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
{-# HLINT ignore "Redundant $" #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# LANGUAGE InstanceSigs #-}

module FD.OvertonFD (
  OvertonFD,
  fd_objective,
  fd_domain,
  FDVar,
  OConstraint(..),
  lookup,
  OPlus((:+)),
) where

import Prelude hiding (lookup)
import Data.Maybe (fromJust,isJust)
import Control.Monad.State.Lazy
import Control.Monad.Trans
import qualified Data.Map as Map
import Data.Map ((!), Map)
import Control.Monad (liftM,(<=<), replicateM, when)

import FD.Domain as Domain

import FD.Debug
import Solver (Solver (..))

--------------------------------------------------------------------------------
-- Solver instance -------------------------------------------------------------
--------------------------------------------------------------------------------

data OConstraint =
    OHasValue FDVar Int -- yes
  | OSame FDVar FDVar -- yes
  | ODiff FDVar FDVar -- yes
  | OLess FDVar FDVar -- yes
  | OLessEq FDVar FDVar -- yes
  | OAdd FDVar FDVar FDVar -- no
  | OSub FDVar FDVar FDVar -- no
  | OMult FDVar FDVar FDVar -- no
  | OAbs FDVar FDVar -- no
  | OInDom FDVar (Int, Int) -- yes
  | OPlusNeq FDVar FDVar Int
  | OLtConst FDVar Int
  | OGtConst FDVar Int
  deriving (Show,Eq)

instance Solver OvertonFD where
  type Constraint OvertonFD = OConstraint

  type Term OvertonFD = FDVar

  type Label OvertonFD = FDState

  newvar :: OvertonFD (Solver.Term OvertonFD)
  newvar = newVar ()
  addCons :: Solver.Constraint OvertonFD -> OvertonFD Bool
  addCons = addOverton
  run :: OvertonFD a -> a
  run = runOverton
  mark :: OvertonFD (Label OvertonFD)
  mark = get
  goto :: Label OvertonFD -> OvertonFD ()
  goto = put

data OPlus = FDVar :+ Int 

-- instance Term OvertonFD FDVar where
--   newvar        = newVar ()
--   type Help OvertonFD FDVar = ()
--   help _ _ = ()

-- instance EnumTerm OvertonFD FDVar where
--   type TermBaseType OvertonFD FDVar = Int
--   getDomain = fd_domain
--   setValue var val = return [var `OHasValue` val]

--------------------------------------------------------------------------------
-- Constraints -----------------------------------------------------------------
--------------------------------------------------------------------------------

addOverton :: OConstraint -> OvertonFD Bool
addOverton (OHasValue v i) = v `hasValue` i
addOverton (OSame a b) = a `same` b
addOverton (ODiff a b) = a `different` b
addOverton (OLess a b) = a .<. b
addOverton (OLessEq a b) = a .<=. b
addOverton (OAdd a b c) = addSum a b c
addOverton (OSub a b c) = addSub a b c
addOverton (OMult a b c) = addMult a b c
addOverton (OAbs a b) = addAbs a b
addOverton (OInDom a r) = do 
    d <- lookup a 
    let d' = d `intersection` (toDomain r)
    if not (Domain.null d') then update a d' 
    else return False
addOverton (OPlusNeq a b n) = undefined
addOverton (OLtConst var c) = var .< c
addOverton (OGtConst var c) = var .> c


fd_domain :: FDVar -> OvertonFD [Int]
fd_domain v = do d <- lookup v
                 return $ elems d

fd_objective :: OvertonFD FDVar
fd_objective =
  do objective <$> get

--------------------------------------------------------------------------------

-- The FD monad
newtype OvertonFD a = OvertonFD { unFD :: State FDState a }
    deriving (Monad, Applicative, Functor, MonadState FDState)

-- FD variables
newtype FDVar = FDVar { unFDVar :: Int } deriving (Ord, Eq, Show)

type VarSupply = FDVar

data VarInfo = VarInfo
     { delayedConstraints :: OvertonFD Bool, domain :: Domain }

instance Show VarInfo where
  show x = show $ domain x

type VarMap = Map FDVar VarInfo

data FDState = FDState
     { varSupply :: VarSupply, varMap :: VarMap, objective :: FDVar }
     deriving Show

instance Eq FDState where
  s1 == s2 = f s1 == f s2
           where f s = head $ elems $ domain $ varMap s ! (objective s)

instance Ord FDState where
  compare s1 s2  = compare (f s1) (f s2)
           where f s = head $ elems $  domain $ varMap s ! (objective s)

  -- TOM: inconsistency is not observable within the OvertonFD monad
consistentFD :: OvertonFD Bool
consistentFD = return True

-- Run the FD monad and produce a lazy list of possible solutions.
runOverton :: OvertonFD a -> a
runOverton fd =
  let j = evalState (unFD fd) initState
      in j

initState :: FDState
initState = FDState { varSupply = FDVar 0, varMap = Map.empty, objective = FDVar 0 }

-- Get a new FDVar
newVar :: ToDomain a => a -> OvertonFD FDVar
newVar d = do
    s <- get
    let v = varSupply s
    put $ s { varSupply = FDVar (unFDVar v + 1) }
    modify $ \s ->
        let vm = varMap s
            vi = VarInfo {
                delayedConstraints = return True,
                domain = toDomain d}
        in
        s { varMap = Map.insert v vi vm }
    return v

newVars :: ToDomain a => Int -> a -> OvertonFD [FDVar]
newVars n d = replicateM n (newVar d)

-- Lookup the current domain of a variable.
lookup :: FDVar -> OvertonFD Domain
lookup x = do
    s <- get
    return . domain $ varMap s ! x

-- Update the domain of a variable and fire all delayed constraints
-- associated with that variable.
update :: FDVar -> Domain -> OvertonFD Bool
update x i = do
    debug (show x ++ " <- " ++ show i)  (return ())
    s <- get
    let vm = varMap s
    let vi = vm ! x
    debug ("where old domain = " ++ show (domain vi)) (return ())
    put $ s { varMap = Map.insert x (vi { domain = i}) vm }
    delayedConstraints vi

-- | Add a new constraint for a variable to the constraint store.
addConstraint :: FDVar -> OvertonFD Bool -> OvertonFD ()
addConstraint x constraint = do
    s <- get
    let vm = varMap s
    let vi = vm ! x
    let cs = delayedConstraints vi
    put $ s { varMap =
        Map.insert x (vi { delayedConstraints = do b <- cs
                                                   if b then constraint
                                                        else return False}) vm }

-- Useful helper function for adding binary constraints between FDVars.
type BinaryConstraint = FDVar -> FDVar -> OvertonFD Bool
addBinaryConstraint :: BinaryConstraint -> BinaryConstraint
addBinaryConstraint f x y = do
    let constraint  = f x y
    b <- constraint
    when b (do addConstraint x constraint
               addConstraint y constraint)
    return b

type TernaryConstraint = FDVar -> FDVar -> FDVar -> OvertonFD Bool 
addTernaryConstraint :: TernaryConstraint -> TernaryConstraint
addTernaryConstraint f x y z = do 
    let constraint = f x y z 
    b <- constraint 
    when b (do addConstraint x constraint
               addConstraint y constraint
               addConstraint z constraint)
    return b

-- Constrain a variable to a particular value.
hasValue :: FDVar -> Int -> OvertonFD Bool
var `hasValue` val = do
    vals <- lookup var
    if val `member` vals
       then do let i = singleton val
               if (i /= vals)
                  then update var i
                  else return True
       else return False

infix 4 .<
(.<) :: FDVar -> Int -> OvertonFD Bool 
(.<) var top = do 
    vals <- lookup var 
    let vals' = filterLessThan top vals 
    if not (Domain.null vals') then (if vals' /= vals then update var vals' else return True) else return False

infix 4 .>
(.>) :: FDVar -> Int -> OvertonFD Bool 
(.>) var top = do 
    vals <- lookup var 
    let vals' = filterGreaterThan top vals 
    if not (Domain.null vals') then (if vals' /= vals then update var vals' else return True) else return False

-- Constrain two variables to have the same value.
same :: FDVar -> FDVar -> OvertonFD Bool
same = addBinaryConstraint $ \x y -> do
    debug "inside same" $ return ()
    xv <- lookup x
    yv <- lookup y
    debug (show xv ++ " same " ++ show yv) $ return ()
    let i = xv `intersection` yv
    if not $ Domain.null i
       then whenwhen (i /= xv)  (i /= yv) (update x i) (update y i)
       else return False

whenwhen :: Monad m => Bool -> Bool -> m Bool -> m Bool -> m Bool
whenwhen c1 c2 a1 a2
  | c1 = do b1 <- a1
            if b1
               then if c2
                       then a2
                       else return True
               else return False
  | c2 = a2
  | otherwise = return True

-- Constrain two variables to have different values.
different :: FDVar  -> FDVar  -> OvertonFD Bool
different = addBinaryConstraint $ \x y -> do
    xv <- lookup x
    yv <- lookup y
    if not (isSingleton xv) || not (isSingleton yv) || xv /= yv
       then whenwhen (isSingleton xv && xv `isSubsetOf` yv)
                     (isSingleton yv && yv `isSubsetOf` xv)
                     (update y (yv `difference` xv))
                     (update x (xv `difference` yv))
       else return False

-- Constrain one variable to have a value less than the value of another
-- variable.
infix 4 .<.
(.<.) :: FDVar -> FDVar -> OvertonFD Bool
(.<.) = addBinaryConstraint $ \x y -> do
    xv <- lookup x
    yv <- lookup y
    let xv' = filterLessThan (findMax yv) xv
    let yv' = filterGreaterThan (findMin xv) yv
    if  not $ Domain.null xv'
        then if not $ Domain.null yv'
                then whenwhen (xv /= xv') (yv /= yv') (update x xv') (update y yv')
                else return False
        else return False



-- Constrain one variable to have a value less than or equal to the value of another 
-- variable.
infix 4 .<=.
(.<=.) :: FDVar -> FDVar -> OvertonFD Bool
(.<=.) = addBinaryConstraint $ \x y -> do
    xv <- lookup x
    yv <- lookup y
    let xv' = filterLessThan (1 + findMax yv) xv
    let yv' = filterGreaterThan ((findMin xv) - 1) yv
    if  not $ Domain.null xv'
        then if not $ Domain.null yv'
                then whenwhen (xv /= xv') (yv /= yv') (update x xv') (update y yv')
                else return False
        else return False

{-
-- Get all solutions for a constraint without actually updating the
-- constraint store.
solutions :: OvertonFD s a -> OvertonFD s [a]
solutions constraint = do
    s <- get
    return $ evalStateT (unFD constraint) s

-- Label variables using a depth-first left-to-right search.
labelling :: [FDVar s] -> OvertonFD s [Int]
labelling = mapM label where
    label var = do
        vals <- lookup var
        val <- OvertonFD . lift $ elems vals
        var `hasValue` val
        return val
-}

dump :: [FDVar] -> OvertonFD [Domain]
dump = mapM lookup


constraint1 :: FDVar -> FDVar -> FDVar -> (Domain -> Domain -> Domain) -> OvertonFD Bool
constraint1 z x y getDomain = do
        xv <- lookup x
        yv <- lookup y
        zv <- lookup z
        let znew = debug "binaryArith:intersection" $ (debug "binaryArith:zv" $ zv) `intersection` (debug "binaryArith:getDomain" $ getDomain xv yv)
        debug ("binaryArith:" ++ show z ++ " before: "  ++ show zv ++ show "; after: " ++ show znew) (return ())
        if debug "binaryArith:null?" $ not $ Domain.null (debug "binaryArith:null?:znew" $ znew)
           then if (znew /= zv)
                   then debug ("binaryArith:update") $ update z znew
                   else return True
           else return False

addArithmeticConstraint ::
    (Domain -> Domain -> Domain) ->
    (Domain -> Domain -> Domain) ->
    (Domain -> Domain -> Domain) ->
    FDVar -> FDVar -> FDVar -> OvertonFD Bool
addArithmeticConstraint getZDomain getXDomain getYDomain x y z = do
    xv <- lookup x
    yv <- lookup y
    let constraint = constraint1
    -- let constraint z x y getDomain = do
    --     xv <- lookup x
    --     yv <- lookup y
    --     zv <- lookup z
    --     let znew = debug "binaryArith:intersection" $ (debug "binaryArith:zv" $ zv) `intersection` (debug "binaryArith:getDomain" $ getDomain xv yv)
    --     debug ("binaryArith:" ++ show z ++ " before: "  ++ show zv ++ show "; after: " ++ show znew) (return ())
    --     if debug "binaryArith:null?" $ not $ Domain.null (debug "binaryArith:null?:znew" $ znew)
    --        then if (znew /= zv) 
    --                then debug ("binaryArith:update") $ update z znew
    --                else return True
    --        else return False
    let zConstraint = debug "binaryArith: zConstraint" $ constraint z x y getZDomain
        xConstraint = debug "binaryArith: xConstraint" $ constraint x z y getXDomain
        yConstraint = debug "binaryArith: yConstraint" $ constraint y z x getYDomain
    debug ("addBinaryArith: z x") (return ())
    addConstraint z xConstraint
    debug ("addBinaryArith: z y") (return ())
    addConstraint z yConstraint
    debug ("addBinaryArith: x z") (return ())
    addConstraint x zConstraint
    debug ("addBinaryArith: x y") (return ())
    addConstraint x yConstraint
    debug ("addBinaryArith: y z") (return ())
    addConstraint y zConstraint
    debug ("addBinaryArith: y x") (return ())
    addConstraint y xConstraint
    debug ("addBinaryArith: done") (return ())
    return True


constraint2 :: FDVar -> FDVar -> (Domain -> Domain) -> OvertonFD Bool
constraint2 z x getDomain = do
        xv <- lookup x
        zv <- lookup z
        let znew = zv `intersection` (getDomain xv)
        debug ("unaryArith:" ++ show z ++ " before: "  ++ show zv ++ show "; after: " ++ show znew) (return ())
        if not $ Domain.null znew
           then if (znew /= zv)
                   then update z znew
                   else return True
           else return False

-- | Add constraint (z = op x) for var z
-- order is getZDom getXDom x z
addUnaryArithmeticConstraint :: (Domain -> Domain) -> (Domain -> Domain) -> FDVar -> FDVar -> OvertonFD Bool
addUnaryArithmeticConstraint getZDomain getXDomain x z = do
    -- xv <- lookup x
    let constraint = constraint2
    let zConstraint = constraint z x getZDomain
        xConstraint = constraint x z getXDomain
    addConstraint z xConstraint
    addConstraint x zConstraint
    return True

addSum :: FDVar -> FDVar -> FDVar -> OvertonFD Bool
-- addSum = addArithmeticConstraint getDomainPlus getDomainMinus getDomainMinus
addSum = addTernaryConstraint $ \x y z -> do 
    dx <- lookup x 
    dy <- lookup y
    dz <- lookup z 
    let dxNew = dx `intersection` getDomainPlus  dy dz
        dyNew = dy `intersection` getDomainMinus dx dz 
        dzNew = dz `intersection` getDomainMinus dx dy
    if Domain.null dxNew || Domain.null dyNew || Domain.null dzNew 
        then return False 
        else (do
          bx <- if (dx /= dxNew) then (update x dxNew) else (return True)
          by <- if (dy /= dyNew) then (update y dyNew) else (return True)
          bz <- if (dz /= dzNew) then (update z dzNew) else (return True)
          return $ bx && by && bz)

        
          
                        


{-
whenwhen :: Monad m => Bool -> Bool -> m Bool -> m Bool -> m Bool
whenwhen c1 c2 a1 a2
  | c1 = do b1 <- a1
            if b1
               then if c2
                       then a2
                       else return True
               else return False
  | c2 = a2
  | otherwise = return True

-}
{-
if  not $ Domain.null xv'
        then if not $ Domain.null yv'
                then whenwhen (xv /= xv') (yv /= yv') (update x xv') (update y yv')
                else return False
        else return False
-}
addSub :: FDVar -> FDVar -> FDVar -> OvertonFD Bool
addSub = addArithmeticConstraint getDomainMinus getDomainPlus (flip getDomainMinus)

addMult :: FDVar -> FDVar -> FDVar -> OvertonFD Bool
addMult = addArithmeticConstraint getDomainMult getDomainDiv getDomainDiv

addAbs :: FDVar -> FDVar -> OvertonFD Bool
addAbs = addUnaryArithmeticConstraint absDomain (\z -> mapDomain z (\i -> [i,-i]))

addShift :: Int -> FDVar -> FDVar -> OvertonFD Bool
addShift i = addUnaryArithmeticConstraint (`shiftDomain` (-i)) (`shiftDomain` (i))

getDomainPlus :: Domain -> Domain -> Domain
getDomainPlus xs ys = toDomain (zl, zh) where
    zl = findMin xs + findMin ys
    zh = findMax xs + findMax ys

getDomainMinus :: Domain -> Domain -> Domain
getDomainMinus xs ys = toDomain (zl, zh) where
    zl = findMin xs - findMax ys
    zh = findMax xs - findMin ys

getDomainMult :: Domain -> Domain -> Domain
getDomainMult xs ys = (\d -> debug ("multDomain" ++ show d ++ "=" ++ show xs ++ "*" ++ show ys ) d) $ toDomain (zl, zh) where
    zl = minimum products
    zh = maximum products
    products = [x * y |
        x <- [findMin xs, findMax xs],
        y <- [findMin ys, findMax ys]]

getDomainDiv :: Domain -> Domain -> Domain
getDomainDiv xs ys = toDomain (zl, zh) where
    zl = minimum quotientsl
    zh = maximum quotientsh
    quotientsl = [if y /= 0 then x `div` y else minBound |
        x <- [findMin xs, findMax xs],
        y <- [findMin ys, findMax ys]]
    quotientsh = [if y /= 0 then x `div` y else maxBound |
        x <- [findMin xs, findMax xs],
        y <- [findMin ys, findMax ys]]

    


{-
if not (isSingleton xv) || not (isSingleton yv) || xv /= yv
       then whenwhen (isSingleton xv && xv `isSubsetOf` yv)
                     (isSingleton yv && yv `isSubsetOf` xv)
                     (update y (yv `difference` xv))
                     (update x (xv `difference` yv))
       else return False
-}
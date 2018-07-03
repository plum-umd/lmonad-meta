{-@ LIQUID "--reflection"  @-}
module TableInfoErase where

import Labels 
import Prelude hiding (Maybe(..), fromJust, isJust)
import Programs 

import ProofCombinators 



{-@ lookupTableInfoErase :: (Eq l, Label l) => l:l -> n:TName -> db:DB l -> 
   {lookupTableInfo n db == lookupTableInfo n (εDB l db)} @-}
lookupTableInfoErase :: (Eq l, Label l) => l -> TName -> DB l -> Proof 
lookupTableInfoErase l n [] 
  =   lookupTableInfo n [] 
  ==. lookupTableInfo n (εDB l [])
  *** QED 

lookupTableInfoErase l n (Pair n' (Table ti r):ts) 
  | n == n'
  =   lookupTableInfo n (Pair n' (Table ti r):ts) 
  ==. case lookupTable n (Pair n' (Table ti r):ts) of 
       Nothing -> Nothing 
       Just (Table tinfo _) -> Just tinfo
  ==. case Just (Table ti r) of 
       Nothing -> Nothing 
       Just (Table tinfo _) -> Just tinfo
  ==. Just ti 
  ==. case Just (Table ti (if tableLabel ti `canFlowTo` l then (εRows l ti r) else [])) of 
       Nothing -> Nothing
       Just (Table tinfo _) -> Just tinfo
  ==. case lookupTable n (Pair n' (Table ti (if tableLabel ti `canFlowTo` l then (εRows l ti r) else [])):εDB l ts) of 
       Nothing -> Nothing
       Just (Table tinfo _) -> Just tinfo
  ==. lookupTableInfo n (Pair n' (Table ti (if tableLabel ti `canFlowTo` l then (εRows l ti r) else [])):εDB l ts )
  ==. lookupTableInfo n (Pair n' (εTable l (Table ti r)):εDB l ts )
  ==. lookupTableInfo n (εDB l (Pair n' (Table ti r):ts))
  *** QED 


lookupTableInfoErase l n (Pair n' (Table ti r):ts) 
  =   lookupTableInfo n (Pair n' (Table ti r):ts) 
  ==. case lookupTable n (Pair n' (Table ti r):ts) of 
       Nothing -> Nothing 
       Just (Table tinfo _) -> Just tinfo
  ==. case lookupTable n ts of 
       Nothing -> Nothing 
       Just (Table tinfo _) -> Just tinfo
  ==. lookupTableInfo n ts  
       ? lookupTableInfoErase l n ts 
  ==. lookupTableInfo n (εDB l ts) 
  ==. case lookupTable n (εDB l ts) of 
       Nothing -> Nothing
       Just (Table tinfo _) -> Just tinfo
  ==. case lookupTable n (Pair n' (Table ti (if tableLabel ti `canFlowTo` l then (εRows l ti r) else [])):εDB l ts) of 
       Nothing -> Nothing
       Just (Table tinfo _) -> Just tinfo
  ==. lookupTableInfo n (Pair n' (Table ti (if tableLabel ti `canFlowTo` l then (εRows l ti r) else [])):εDB l ts)
  ==. lookupTableInfo n (Pair n' (Table ti (if tableLabel ti `canFlowTo` l then (εRows l ti r) else [])):εDB l ts)
  ==. lookupTableInfo n (Pair n' (εTable l (Table ti r)):εDB l ts )
  ==. lookupTableInfo n (εDB l (Pair n' (Table ti r):ts))
  *** QED 

-- {-@ tailTInfoEqual 
--  :: Eq l 
--  => n : TName
--  -> {n1 : TName | n /= n1}
--  -> t : Table l
--  -> ts : DB l
--  -> {(lookupTableInfo n ts) == (lookupTableInfo n ((Pair n1 t):ts))}
--  @-}
--  -- {(lookupTableInfo n ((Pair n' t):ts)) == (lookupTableInfo n ts)}
-- tailTInfoEqual :: Eq l => TName -> TName -> Table l -> DB l -> Proof
-- tailTInfoEqual n n' t ts = 
--     (   lookupTable n (Pair n' t:ts)
--     ==. lookupTable n ts
--     *** QED)
--     &&& assert (lookupTableInfo n (Pair n' t:ts) == lookupTableInfo n ts)


{-@ tailTInfoEqual 
 :: Eq l 
 => n : TName 
 -> {n1 : TName | n /= n1}
 -> t : Table l 
 -> db : {DB l | head db == Pair n1 t && len db > 0} 
 -> {lookupTableInfo n db == lookupTableInfo n (tail db)}
 @-}
 -- {(lookupTableInfo n ((Pair n' t):ts)) == (lookupTableInfo n ts)}
tailTInfoEqual :: Eq l => TName -> TName -> Table l -> DB l -> Proof
tailTInfoEqual n n' t db@(Pair _ _:ts) = 
    (   lookupTable n db
    ==. lookupTable n (tail db)
    *** QED)
    &&& assert (lookupTableInfo n db == lookupTableInfo n ts)

{-@ tinfoEqual
 :: n : TName
 -> {n' : TName | n == n'}
 -> db : {DB l | len db > 0}
 -> ti : {TInfo l | Just ti == lookupTableInfo n db}
 -> rs : [Row l]
 -> ti' : {TInfo l | head db == Pair n' (Table ti' rs)}
 -> {ti == ti'}
 @-}
tinfoEqual :: TName -> TName -> DB l -> TInfo l -> [Row l] -> TInfo l -> Proof
tinfoEqual n n' db@(_:ts) ti rs ti'
    =   lookupTableInfo n db
        ? ( lookupTable n db
        ==! Just (Table ti' rs)
        *** QED)
    ==. Just ti'
    ==. Just ti
    *** QED


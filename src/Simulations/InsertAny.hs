{-@ LIQUID "--reflection"  @-}
{-@ infix :  @-}

module Simulations.InsertAny where

import ProofCombinators
import Labels 
import Programs 
import Predicates 

import Idempotence 

import Prelude hiding (Maybe(..), fromJust, isJust)



{-@ simulationsInsertAny  
  :: Label l => l:l 
  -> db:DB l 
  -> n:TName
  -> r:Row l 
  -> ti:{TInfo l | (not (canFlowTo (tableLabel ti) l)) && (Just ti == lookupTableInfo n db)} 
  -> { εDB l (insertDB db n r) == εDB l db } 
  @-}
simulationsInsertAny :: (Label l, Eq l) 
  => l -> DB l -> TName -> Row l -> TInfo l  -> Proof

simulationsInsertAny l [] n p _ 
  =   εDB l (insertDB (εDB l []) n p) 
  ==. εDB l (insertDB [] n p) 
  *** QED 

simulationsInsertAny l ((Pair n' t@(Table ti rs)):ts) n p _ 
  | n == n', not (tableLabel ti `canFlowTo` l)  
  =   εDB l (insertDB (εDB l ((Pair n' t):ts)) n p) 
  ==. εDB l (insertDB (Pair n' (εTable l t):εDB l ts) n p) 
  ==. εDB l (insertDB (Pair n' (Table ti []):εDB l ts) n p) 
  ==. εDB l (Pair n' (insertTable (Table ti []) p):εDB l ts) 
  ==. εDB l (Pair n' (Table ti []):εDB l ts) 
  ==. Pair n' (εTable l (Table ti [])) :εDB l (εDB l ts) 
  ==. Pair n' (Table ti [])            :εDB l (εDB l ts) 
       ? εDBIdempotent l ts 
  ==. Pair n' (Table ti []):εDB l ts 
  ==. Pair n' (εTable l (insertTable t p)):εDB l ts 
  ==. εDB l (Pair n' (insertTable t p):ts) 
  ==. εDB l (insertDB ((Pair n' t):ts) n p) 
  *** QED 


simulationsInsertAny l (Pair n' (Table ti' r):ts) n p ti 
  | n == n'
  =   ti   
  ==. fromJust (Just ti)
  ==. fromJust (lookupTableInfo n (Pair n' (Table ti' r):ts))
  ==. fromJust (case lookupTable n (Pair n' (Table ti' r):ts) of {
                 Just (Table ti' _) -> Just ti' ; 
                 Nothing -> Nothing} )
  ==. fromJust (Just ti')
      ? assert (ti == ti')
      ? assert (not (tableLabel ti `canFlowTo` l))
  ==. ti' 
  *** QED 



simulationsInsertAny l ((Pair n' t@(Table ti rs)):ts) n p ti' 
  =   εDB l (insertDB (εDB l (Pair n' t:ts)) n p) 
  ==. εDB l (insertDB (Pair n' (εTable l t):εDB l ts) n p) 
  ==. εDB l (Pair n' (εTable l t):insertDB (εDB l ts) n p) 
  ==. Pair n' (εTable l (εTable l t)):(εDB l (insertDB (εDB l ts) n p))
       ? (    lookupTableInfo n (Pair n' (Table ti rs):ts)
          ==. case lookupTable n (Pair n' (Table ti rs):ts) of 
                Nothing -> Nothing
                Just (Table ti _) -> Just ti 
          ==. case lookupTable n ts of 
                Nothing -> Nothing
                Just (Table ti _) -> Just ti 
          ==. lookupTableInfo n ts
          *** QED 
         ) &&& assert (lookupTableInfo n (Pair n' (Table ti rs):ts) == lookupTableInfo n ts)
           &&& assert (ti' == fromJust (lookupTableInfo n ts))
           &&& assert (not (canFlowTo (tableLabel ti') l))
           &&& simulationsInsertAny l ts n p ti' 
           &&& εTableIdempotent l t 
  ==. Pair n' (εTable l t):(εDB l (insertDB ts n p))
  ==. εDB l (Pair n' t:insertDB ts n p) 
  ==. εDB l (insertDB (Pair n' t:ts) n p) 
  *** QED 


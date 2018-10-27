{-@ LIQUID "--reflection"  @-}
{-@ infix :  @-}

module Simulations.DeleteAll where

import ProofCombinators
import Labels 
import Programs 

import Idempotence 

import Prelude hiding (Maybe(..), fromJust, isJust)



{-@ simulationsDeleteAll  
  :: Label l => l:l 
  -> db:DB l 
  -> n:TName
  -> p:Pred l
  -> t:{Table l | (not (canFlowTo (tableLabel (tableInfo t)) l)) && (Just t == lookupTable n db)} 
  -> { εDB l (deleteDB (εDB l db) n p) == εDB l (deleteDB db n p) 
    && εDB l db == εDB l (deleteDB db n p) 
    && εDB l db == εDB l (deleteDB (εDB l db) n p)} 
  @-}
simulationsDeleteAll :: (Label l, Eq l) 
  => l -> DB l -> TName -> Pred l -> Table l  -> Proof

simulationsDeleteAll l [] n p _ 
  =   εDB l (deleteDB (εDB l []) n p) 
  ==. εDB l (deleteDB [] n p) 
  *** QED 


simulationsDeleteAll l ((Pair n' t@(Table ti rs)):ts) n p _ 
  | n == n', not (tableLabel ti `canFlowTo` l)  
  =   εDB l (deleteDB (εDB l ((Pair n' t):ts)) n p) 
  ==. εDB l (deleteDB (Pair n' (εTable l t):εDB l ts) n p) 
  ==. εDB l (deleteDB (Pair n' (Table ti []):εDB l ts) n p) 
  ==. εDB l (Pair n' (Table ti (deleteRaws p [])):εDB l ts) 
  ==. εDB l (Pair n' (Table ti []):εDB l ts) 
  ==. Pair n' (εTable l (Table ti [])) :εDB l (εDB l ts) 
  ==. Pair n' (Table ti [])            :εDB l (εDB l ts) 
       ? εDBIdempotent l ts 
  ==. Pair n' (Table ti []):εDB l ts 
  ==. Pair n' (εTable l (Table ti (deleteRaws p rs))):εDB l ts 
  ==. εDB l (Pair n' (Table ti (deleteRaws p rs)):ts) 
  ==. εDB l (deleteDB ((Pair n' t):ts) n p) 
  *** QED 


simulationsDeleteAll l (Pair n' t':ts) n p t 
  | n == n'
  =   t
  ==. fromJust (lookupTable n (Pair n' t':ts))
  ==. fromJust (Just t')
      ? assert (t == t')
      ? assert (not (tableLabel (tableInfo t) `canFlowTo` l))
  ==. t' 
  *** QED 



simulationsDeleteAll l ((Pair n' t@(Table ti rs)):ts) n p ti' 
  =   εDB l (deleteDB (εDB l (Pair n' t:ts)) n p) 
  ==. εDB l (deleteDB (Pair n' (εTable l t):εDB l ts) n p) 
  ==. εDB l (Pair n' (εTable l t):deleteDB (εDB l ts) n p) 
  ==. Pair n' (εTable l (εTable l t)):(εDB l (deleteDB (εDB l ts) n p))
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
           &&& assert (ti' == fromJust (lookupTable n ts))
           &&& assert (not (canFlowTo (tableLabel (tableInfo ti')) l))
           &&& simulationsDeleteAll l ts n p ti' 
           &&& εTableIdempotent l t 
  ==. Pair n' (εTable l t):(εDB l (deleteDB ts n p))
  ==. εDB l (Pair n' t:deleteDB ts n p) 
  ==. εDB l (deleteDB (Pair n' t:ts) n p) 
  *** QED 




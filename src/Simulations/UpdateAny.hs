{-@ LIQUID "--reflection"  @-}

module Simulations.UpdateAny (simulationsUpdateAny)  where

import ProofCombinators
import Labels 
import Programs 

import Idempotence 
import Simulations.Terms 

import Prelude hiding (Maybe(..), fromJust, isJust)


{-@ simulationsUpdateAny  
  :: Label l 
  => l:l -> lc:{l | not (canFlowTo lc l) } 
  -> db:DB l 
  -> n:{TName | isJust (lookupTable n db) }
  -> p:Pred l
  -> l1:l 
  -> v1:{t:Term l | isDBValue t && ςTerm t }
  -> l2:l  
  -> v2:{t:Term l | isDBValue t && ςTerm t } 
  -> t:{Table l | (Just t == lookupTable n db) && updateLabelCheck lc t p l1 v1 l2 v2} 
  -> { εDB l db == εDB l (updateDB db n p v1 v2) } 
  @-}
  
simulationsUpdateAny :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred l -> l -> Term l -> l -> Term l -> Table l  -> Proof
simulationsUpdateAny l lc [] n p l1 v1 l2 v2 ti 
  = εDB l [] == εDB l (updateDB [] n p v1 v2) *** QED 


simulationsUpdateAny l lc ((Pair n' t@(Table ti rs)):ts) n p l1 v1 l2 v2 t' 
  | n == n'
  =  (Just t' ==. 
      lookupTable n ((Pair n' (Table ti rs)):ts) ==. 
      Just t 
      *** QED)
  &&& (εDB l (updateDB ((Pair n' (Table ti rs)):ts) n p v1 v2)
  ==. εDB l (Pair n' (Table ti (updateRows p v1 v2 rs)):ts)
  ==. Pair n' (εTable l (Table ti (updateRows p v1 v2 rs))):εDB l ts
      ? assert (updateLabelCheck lc t p l1 v1 l2 v2)
      ? simulationsUpdateRows l lc (lfTable p t) ti p l1 v1 l2 v2 rs
  ==. Pair n' (εTable l (Table ti rs)):εDB l ts 
  ==. εDB l (Pair n' (Table ti rs)    :ts) 
  *** QED) 


simulationsUpdateAny l lc (Pair n' t:ts) n p l1 v1 l2 v2 t' 
  =   (Just t' ==. 
      lookupTable n ((Pair n' t):ts) ==. 
      lookupTable n ts
      *** QED)
  &&& (εDB l (updateDB ((Pair n' t):ts) n p v1 v2)
  ==. εDB l (Pair n' t:updateDB ts n p v1 v2)
  ==. Pair n' (εTable l t):εDB l (updateDB ts n p v1 v2)
      ? simulationsUpdateAny l lc ts n p l1 v1 l2 v2 t'
  ==. Pair n' (εTable l t):εDB l ts 
  ==. εDB l (Pair n' t    :ts) 
  *** QED)  

{-@ simulationsUpdateRows
  :: (Label l, Eq l)
  => l:l -> lc:{l | not (canFlowTo lc l) } -> lf:l
  -> ti:TInfo l 
  -> p:Pred l
  -> l1:l 
  -> v1: {t:Term l | isDBValue t && ςTerm t } 
  -> l2:l 
  -> v2: {t:Term l | isDBValue t && ςTerm t } 
  -> rs:{[Row l] | (updateRowsCheck lc lf ti p l1 v1 l2 v2 rs) } 
  -> { ( εRows l ti rs = εRows l ti (updateRows p v1 v2 rs)) } / [len rs] @-}
simulationsUpdateRows
  :: (Label l, Eq l)
  => l -> l -> l -> TInfo l -> Pred l -> l -> Term l -> l -> Term l -> [Row l] -> Proof 
simulationsUpdateRows l lc lφ ti p l1 v1 l2 v2 [] 
  =   εRows l ti (updateRows p v1 v2 [])
  ==. εRows l ti []
  *** QED   

simulationsUpdateRows l lc lφ ti p l1 v1 l2 v2 (r:rs) 
  =   εRows l ti (updateRows p v1 v2 (r:rs))
  ==. εRows l ti (updateRow p v1 v2 r :updateRows p v1 v2 rs)
  ==. εRow l ti (updateRow p v1 v2 r):εRows l ti (updateRows p v1 v2 rs)
      ? assert (updateRowsCheck lc lφ ti p l1 v1 l2 v2 (r:rs))
      ? simulationsUpdateRows l lc lφ ti p l1 v1 l2 v2 rs
      ? simulationsUpdateRow  l lc lφ ti p l1 v1 l2 v2 r
  ==. εRow l ti r:εRows l ti rs
  ==. εRows l ti (r:rs)
  *** QED   

{-@ simulationsUpdateRow
  :: (Label l, Eq l)
  => l:l -> lc:{l | not (canFlowTo lc l) } -> lf:l 
  -> ti:TInfo l 
  -> p:Pred l
  -> l1:l 
  -> v1: {t:Term l | isDBValue t && ςTerm t }
  -> l2:l 
  -> v2: {t:Term l | isDBValue t && ςTerm t } 
  -> r: {Row l | (updateRowCheck lc lf ti p l1 v1 l2 v2 r) } 
  -> { ( εRow l ti r = εRow l ti (updateRow p v1 v2 r)) } @-}
simulationsUpdateRow
  :: (Label l, Eq l)
  => l -> l -> l -> TInfo l -> Pred l -> l -> Term l -> l -> Term l -> Row l -> Proof 
simulationsUpdateRow l lc lφ ti p l1 v1 l2 v2 r@(Row k o1 o2) 
  =   εRow l ti r 
      ? assert (updateRowCheck lc lφ ti p l1 v1 l2 v2 r) 
      ? assert (updateRowLabel1 lc lφ ti p l1 v1 l2 v2 r) 
      ? joinCanFlowTo (l1 `join` lc) lφ (field1Label ti)
      ? joinCanFlowTo l1 lc (field1Label ti)
      ? lawFlowTransitivity lc (field1Label ti) l
      ? assert (not (field1Label ti `canFlowTo` l))
  ==. Row k THole THole
  ==. εRow l ti (updateRow p v1 v2 r)
  *** QED 

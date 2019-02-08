{-@ LIQUID "--reflection"  @-}

module Simulations.UpdateAnyNothingJust (simulationsUpdateAnyNothingJust)  where

import ProofCombinators
import Labels 
import Programs 
import Predicates 

import Idempotence 
import Simulations.Terms 

import Prelude hiding (Maybe(..), fromJust, isJust)


{-@ simulationsUpdateAnyNothingJust  
  :: Label l 
  => l:l -> lc:{l | not (canFlowTo lc l) } 
  -> db:DB l 
  -> n:{TName | isJust (lookupTable n db) }
  -> p:Pred
  -> l2:l  
  -> v2:SDBTerm l 
  -> t:{Table l | (Just t == lookupTable n db) && updateLabelCheckNothingJust lc t p l2 v2} 
  -> { εDB l db == εDB l (updateDBNothingJust db n p v2) } 
  @-}

simulationsUpdateAnyNothingJust :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> l -> Term l -> Table l  -> Proof

simulationsUpdateAnyNothingJust l lc [] n p l2 v2 ti
  =   εDB l [] == εDB l (updateDBNothingJust [] n p v2) *** QED

simulationsUpdateAnyNothingJust l lc ((Pair n' t@(Table ti rs)):ts) n p l2 v2 t'
  | n' == n
  = (Just t' ==. 
     lookupTable n ((Pair n' (Table ti rs)):ts) ==. 
     Just t 
     *** QED)
  &&& (εDB l (updateDBNothingJust ((Pair n' (Table ti rs)):ts) n p v2)
  ==. εDB l (Pair n' (Table ti (updateRowsNothingJust p v2 rs)):ts)
  ==. Pair n' (εTable l (Table ti (updateRowsNothingJust p v2 rs))):εDB l ts
      ? assert (updateLabelCheckNothingJust lc t p l2 v2)
      ? simulationsUpdateRowsNothingJust l lc (lfTable p t) ti p l2 v2 rs
  ==. Pair n' (εTable l (Table ti rs)): εDB l ts
  ==. εDB l (Pair n' (Table ti rs) :ts)
  *** QED)

simulationsUpdateAnyNothingJust l lc ((Pair n' t@(Table ti rs)):ts) n p l2 v2 t'
  = (Just t' ==. 
    lookupTable n ((Pair n' t):ts) ==. 
    lookupTable n ts
    *** QED)
  &&& (εDB l (updateDBNothingJust ((Pair n' t):ts) n p v2)
  ==. εDB l (Pair n' t:updateDBNothingJust ts n p v2)
  ==. Pair n' (εTable l t):εDB l (updateDBNothingJust ts n p v2)
      ? simulationsUpdateAnyNothingJust l lc ts n p l2 v2 t'
  ==. Pair n' (εTable l t):εDB l ts
  ==. εDB l (Pair n' t    :ts)
  *** QED)


{-@ simulationsUpdateRowsNothingJust
  :: (Label l, Eq l)
  => l:l -> lc:{l | not (canFlowTo lc l) } -> lf:l
  -> ti:TInfo l 
  -> p:Pred
  -> l2:l 
  -> v2: SDBTerm l 
  -> rs:{[Row l] | (updateRowsCheckNothingJust lc lf ti p l2 v2 rs) } 
  -> { ( εRows l ti rs = εRows l ti (updateRowsNothingJust p v2 rs)) } / [len rs] @-}
simulationsUpdateRowsNothingJust
  :: (Label l, Eq l)
  => l -> l -> l -> TInfo l -> Pred -> l -> Term l -> [Row l] -> Proof
  -- lφ is labelPred/lftable
simulationsUpdateRowsNothingJust l lc lφ ti p l2 v2 []
  =   εRows l ti []
  ==. εRows l ti (updateRowsNothingJust p v2 [])
  *** QED

simulationsUpdateRowsNothingJust l lc lφ ti p l2 v2 (r:rs)
  =   εRows l ti (updateRowsNothingJust p v2 (r:rs))
  ==. εRows l ti (updateRowNothingJust p v2 r : updateRowsNothingJust p v2 rs)
  ==. εRow l ti (updateRowNothingJust p v2 r) : εRows l ti (updateRowsNothingJust p v2 rs)
      ? assert (updateRowsCheckNothingJust lc lφ ti p l2 v2 (r:rs))
      ? simulationsUpdateRowsNothingJust l lc lφ ti p l2 v2 rs
      ? simulationsUpdateRowNothingJust l lc lφ ti p l2 v2 r
  ==. εRow l ti r : εRows l ti rs
  ==. εRows l ti (r:rs)
  *** QED


{-@ simulationsUpdateRowNothingJust
  :: (Label l, Eq l)
  => l:l -> lc:{l | not (canFlowTo lc l) } -> lf:l 
  -> ti:TInfo l 
  -> p:Pred
  -> l2:l 
  -> v2: SDBTerm l 
  -> r: {Row l | (updateRowCheckNothingJust lc lf ti p l2 v2 r) } 
  -> { ( εRow l ti r = εRow l ti (updateRowNothingJust p v2 r)) } @-}

simulationsUpdateRowNothingJust
  :: (Label l, Eq l)
  => l -> l -> l -> TInfo l -> Pred -> l -> Term l -> Row l -> Proof 
simulationsUpdateRowNothingJust l lc lφ ti p l2 v2 r@(Row k v1 _)
  | field1Label ti `canFlowTo` l
  =   εRow l ti r
        ? assert (updateRowCheckNothingJust lc lφ ti p l2 v2 r)
        ? assert (updateRowLabel2 lc lφ ti p (field1Label ti) v1 l2 v2 r)
        ? joinCanFlowTo (l2 `join` lc) lφ (makeValLabel ti v1)
        ? joinCanFlowTo l2 lc (makeValLabel ti v1)
        ? lawFlowTransitivity lc (makeValLabel ti v1) l
        ? assert (not (makeValLabel ti v1 `canFlowTo` l) )
  ==. Row k (εTerm l v1) THole
  ==. εRow l ti (updateRowNothingJust p v2 r)
  *** QED
simulationsUpdateRowNothingJust l lc lφ ti p l2 v2 r@(Row k v1 _)
  =   εRow l ti r
      ? assert (not (field1Label ti `canFlowTo` l))
  ==. Row k THole THole
  ==. εRow l ti (updateRowNothingJust p v2 r)
  *** QED

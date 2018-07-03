{-@ LIQUID "--reflection"  @-}


module Simulations.UpdateRowBySMT where

import ProofCombinators
import Labels 
import Programs 
import Predicates 

import Idempotence 
import Simulations.Terms 

import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsUpdateRowOneErased
  :: (Label l, Eq l)
  => l:l -> lc:{l | canFlowTo lc l } -> lf:l -> elf:l
  -> ti:TInfo l 
  -> p:Pred 
  -> l1:{l | not (canFlowTo (field1Label ti) l && canFlowTo l1 l)}
  -> v1: SDBTerm l 
  -> l2:l 
  -> v2: SDBTerm l 
  -> r: {Row l | (canFlowTo (lfRow p ti r) lf) && (canFlowTo (lfRow p ti (εRow l ti r)) elf) && (not (updateRowCheck lc lf ti p l1 v1 l2 v2 r)) && (updateRowCheck lc elf ti p l1 (if (canFlowTo l1 l) then v1 else THole) l2 (if (canFlowTo l2 l) then v2 else THole) (εRow l ti r)) } 
  -> { εRow l ti r = εRow l ti (updateRow p (if (canFlowTo l1 l) then v1 else THole) (if (canFlowTo l2 l) then v2 else THole) (εRow l ti r)) } @-}
simulationsUpdateRowOneErased 
  :: (Label l, Eq l)
  => l -> l -> l -> l -> TInfo l -> Pred -> l -> Term l -> l -> Term l -> Row l -> Proof 
simulationsUpdateRowOneErased l lc lφ εlφ ti p l1 v1 l2 v2 r@(Row k o1 o2) 
  =   εRow l ti r 
      ? globals
  ==. εRow l ti (updateRow p εv1 εv2 (εRow l ti (Row k o1 o2)))
  *** QED 
    where 
      εrr = εRow l ti r 
      εr  = Row k (εTerm l o1) THole
      εv1 = if (canFlowTo l1 l) then v1 else THole
      εv2 = if (canFlowTo l2 l) then v2 else THole
      εo2 = if makeValLabel ti o1 `canFlowTo` l then (εTerm l v2) else THole
      lφR  = lfRow p ti r  
      lφER = lfRow p ti εrr
      globals =  
          assert (updateRowCheck  lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r))
        ? assert (updateRowLabel1 lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r))
        ? assert (updateRowLabel2 lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r))
        ? assert (not (updateRowCheck lc lφ ti p l1 v1 l2 v2 r))
        ? use (updateRowLabel1 lc lφ ti p l1 v1 l2 v2 r)
        ? use (updateRowLabel2 lc lφ ti p l1 v1 l2 v2 r)
        ? assert (canFlowTo lφR lφ)
        ? assert (canFlowTo lφER εlφ)
        ? joinCanFlowTo (l1 `join` lc) lφ (field1Label ti)
        ? lawFlowTransitivity lφR  lφ (field1Label ti) 
        ? joinCanFlowTo (l1 `join` lc) εlφ (field1Label ti)
        ? lawFlowTransitivity lφER εlφ (field1Label ti) 
        ? joinCanFlowTo l1 lc (field1Label ti)

        ? joinCanFlowTo (l2 `join` lc) lφ (makeValLabel ti v1)
        ? joinCanFlowTo (l2 `join` lc) εlφ (makeValLabel ti v1)
        ? lawFlowTransitivity lφR  lφ (makeValLabel ti v1) 
        ? lawFlowTransitivity lφER εlφ (makeValLabel ti v1) 
        ? joinCanFlowTo l2 lc (makeValLabel ti v1)
        ? joinCanFlowTo (l2 `join` lc) lφ (makeValLabel ti εv1)
        ? joinCanFlowTo (l2 `join` lc) εlφ (makeValLabel ti εv1)
        ? lawFlowTransitivity lφR lφ (makeValLabel ti εv1) 
        ? lawFlowTransitivity lφER εlφ (makeValLabel ti εv1) 

        ? joinCanFlowTo l2 lc (makeValLabel ti v1)
        ? joinCanFlowTo l2 lc (makeValLabel ti εv1)
        ? lawFlowTransitivity lφR lφ l 
        ? lawFlowTransitivity lφER εlφ l 
        ? lawFlowTransitivity l2 (makeValLabel ti o1)  l 
        ? lawFlowTransitivity l2 (makeValLabel ti v1)  l 
        ? lawFlowTransitivity l2 (makeValLabel ti εv1) l 
        ? lawFlowTransitivity l1 (field1Label ti)      l 
        ? lawFlowTransitivity (makeValLabel ti o1) (field1Label ti)      l 
        ? lawFlowTransitivity (makeValLabel ti o1) (makeValLabel ti εv1) l 
        ? lawFlowTransitivity (makeValLabel ti o1) (makeValLabel ti  v1) l 
        ? lawFlowTransitivity (field1Label ti) (makeValLabel ti εv1) l 
        ? lawFlowTransitivity (field1Label ti) (makeValLabel ti  v1) l 
        ? lawFlowTransitivity (makeValLabel ti εv1) (field1Label ti) l 
        ? lawFlowTransitivity (makeValLabel ti v1) (field1Label ti) l 
        ? lawFlowTransitivity (makeValLabel ti o1) (field1Label ti) l 
        ? assert (εTerm l THole == THole)
        ? assert (εTerm l v1 == v1 )  
        ? assert (εTerm l v2 == v2 )  
        ? assert (εTerm l o1 == o1 )  
        ? assert (εTerm l o2 == o2 )  
        ? (evalPred p r *** QED )
        ? (evalPred p (εRow l ti r) *** QED )
        ? (evalPred p εr *** QED )
        ? lawBot (field1Label ti)
        ? lawBot (makeValLabel ti v1)
        ? lawBot (makeValLabel ti εv1)
        ? lawFlowReflexivity (field1Label ti)




{-@ simulationsUpdateRowOne
  :: (Label l, Eq l)
  => l:l -> lc:{l | canFlowTo lc l } -> lf:l -> elf:l
  -> ti:TInfo l 
  -> p:Pred 
  -> l1:{l | not (canFlowTo (field1Label ti) l && canFlowTo l1 l)}
  -> v1: SDBTerm l 
  -> l2:l 
  -> v2: SDBTerm l 
  -> r: {Row l | (canFlowTo (lfRow p ti r) lf) && (canFlowTo (lfRow p ti (εRow l ti r)) elf) && (updateRowCheck lc lf ti p l1 v1 l2 v2 r) && (not (updateRowCheck lc elf ti p l1 (if (canFlowTo l1 l) then v1 else THole) l2 (if (canFlowTo l2 l) then v2 else THole) (εRow l ti r))) } 
  -> { εRow l ti r = εRow l ti (updateRow p v1 v2 r) } @-}
simulationsUpdateRowOne 
  :: (Label l, Eq l)
  => l -> l -> l -> l -> TInfo l -> Pred -> l -> Term l -> l -> Term l -> Row l -> Proof 
simulationsUpdateRowOne l lc lφ εlφ ti p l1 v1 l2 v2 r@(Row k o1 o2) 
  =   εRow l ti r 
      ? globals
  ==. εRow l ti (updateRow p v1 v2 (Row k o1 o2))
  *** QED 
    where 
      εrr = εRow l ti r 
      εr  = Row k (εTerm l o1) THole
      εv1 = if (canFlowTo l1 l) then v1 else THole
      εv2 = if (canFlowTo l2 l) then v2 else THole
      εo2 = if makeValLabel ti o1 `canFlowTo` l then (εTerm l v2) else THole
      lφR  = lfRow p ti r  
      lφER = lfRow p ti εrr
      globals =  
          assert (not (updateRowCheck  lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r)))
        ? use (updateRowLabel1 lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r))
        ? use (updateRowLabel2 lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r))
        ? assert (updateRowCheck lc lφ ti p l1 v1 l2 v2 r)
        ? assert (updateRowLabel1 lc lφ ti p l1 v1 l2 v2 r)
        ? assert (updateRowLabel2 lc lφ ti p l1 v1 l2 v2 r)
        ? assert (canFlowTo lφR lφ)
        ? assert (canFlowTo lφER εlφ)
        ? joinCanFlowTo (l1 `join` lc) lφ (field1Label ti)
        ? lawFlowTransitivity lφR  lφ (field1Label ti) 
        ? joinCanFlowTo (l1 `join` lc) εlφ (field1Label ti)
        ? lawFlowTransitivity lφER εlφ (field1Label ti) 
        ? joinCanFlowTo l1 lc (field1Label ti)

        ? joinCanFlowTo (l2 `join` lc) lφ (makeValLabel ti v1)
        ? joinCanFlowTo (l2 `join` lc) εlφ (makeValLabel ti v1)
        ? lawFlowTransitivity lφR  lφ (makeValLabel ti v1) 
        ? lawFlowTransitivity lφER εlφ (makeValLabel ti v1) 
        ? joinCanFlowTo l2 lc (makeValLabel ti v1)
        ? joinCanFlowTo (l2 `join` lc) lφ (makeValLabel ti εv1)
        ? joinCanFlowTo (l2 `join` lc) εlφ (makeValLabel ti εv1)
        ? lawFlowTransitivity lφR lφ (makeValLabel ti εv1) 
        ? lawFlowTransitivity lφER εlφ (makeValLabel ti εv1) 

        ? joinCanFlowTo l2 lc (makeValLabel ti v1)
        ? joinCanFlowTo l2 lc (makeValLabel ti εv1)
        ? lawFlowTransitivity lφR lφ l 
        ? lawFlowTransitivity lφER εlφ l 
        ? lawFlowTransitivity l2 (makeValLabel ti o1)  l 
        ? lawFlowTransitivity l2 (makeValLabel ti v1)  l 
        ? lawFlowTransitivity l2 (makeValLabel ti εv1) l 
        ? lawFlowTransitivity l1 (field1Label ti)      l 
        ? lawFlowTransitivity (makeValLabel ti o1) (field1Label ti)      l 
        ? lawFlowTransitivity (makeValLabel ti o1) (makeValLabel ti εv1) l 
        ? lawFlowTransitivity (makeValLabel ti o1) (makeValLabel ti  v1) l 
        ? lawFlowTransitivity (field1Label ti) (makeValLabel ti εv1) l 
        ? lawFlowTransitivity (field1Label ti) (makeValLabel ti  v1) l 
        ? lawFlowTransitivity (makeValLabel ti εv1) (field1Label ti) l 
        ? lawFlowTransitivity (makeValLabel ti v1) (field1Label ti) l 
        ? lawFlowTransitivity (makeValLabel ti o1) (field1Label ti) l 
        ? assert (εTerm l THole == THole)
        ? assert (εTerm l v1 == v1 )  
        ? assert (εTerm l v2 == v2 )  
        ? assert (εTerm l o1 == o1 )  
        ? assert (εTerm l o2 == o2 )  
        ? (evalPred p r *** QED )
        ? (evalPred p (εRow l ti r) *** QED )
        ? (evalPred p εr *** QED )
        ? lawBot (field1Label ti)
        ? lawBot (makeValLabel ti v1)
        ? lawBot (makeValLabel ti εv1)
        ? lawFlowReflexivity (field1Label ti)

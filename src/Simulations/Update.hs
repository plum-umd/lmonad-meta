{-@ LIQUID "--reflection"  @-}

module Simulations.Update where --  (simulationsUpdate) where

import ProofCombinators
import Labels 
import Programs 
import Predicates 

import Idempotence 
import Simulations.Terms 

import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsUpdate  
  :: Label l => l:l -> lc:{l | canFlowTo lc l } 
  -> db:DB l 
  -> n:{TName | isJust (lookupTable n db) }
  -> p:Pred
  -> l1:l 
  -> v1:SDBTerm l
  -> l2:l  
  -> v2:SDBTerm l 
  -> t: {Table l | (Just t == lookupTable n db) && (updateLabelCheck lc t p l1 v1 l2 v2)}
  -> εt:{Table l | (Just εt == lookupTable n (εDB l db)) && (updateLabelCheck lc εt p l1 (if (canFlowTo l1 l) then v1 else THole) l2 (if (canFlowTo l2 l) then v2 else THole)) } 
  -> { εDB l (updateDB (εDB l db) n p (if (canFlowTo l1 l) then v1 else THole) (if (canFlowTo l2 l) then v2 else THole)) == εDB l (updateDB db n p v1 v2) } @-}
simulationsUpdate :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> l -> Term l -> l -> Term l -> Table l -> Table l  -> Proof
simulationsUpdate l lc [] n p l1 v1 l2 v2 _ _
  =   εDB l (updateDB [] n p v1 v2) 
  ==. εDB l [] 
  ==. εDB l (updateDB (εDB l []) n p εv1 εv2) 
  *** QED 
  where
    εv1 = if (canFlowTo l1 l) then v1 else THole
    εv2 = if (canFlowTo l2 l) then v2 else THole

simulationsUpdate l lc ((Pair n' t@(Table ti rs)):ts) n p l1 v1 l2 v2 t' εt'
  | n == n' && not (tableLabel ti `canFlowTo` l)
  =   εDB l (updateDB (εDB l ((Pair n' t):ts)) n p εv1 εv2)
  ==. εDB l (updateDB ((Pair n' (εTable l t)):εDB l ts) n p εv1 εv2)
  ==. εDB l (updateDB ((Pair n' (εTable l (Table ti rs))):εDB l ts) n p εv1 εv2)
  ==. εDB l (updateDB ((Pair n' (Table ti [])):εDB l ts) n p εv1 εv2)
  ==. εDB l (Pair n' (Table ti (updateRows p εv1 εv2 [])):εDB l ts)
  ==. Pair n' (εTable l (Table ti [])):(εDB l (εDB l ts))
      ?  εDBIdempotent l ts 
  ==. Pair n' (Table ti []):εDB l ts 
  ==. Pair n' (εTable l (Table ti (updateRows p v1 v2 rs))):εDB l ts 
  ==. εDB l (Pair n' (Table ti (updateRows p v1 v2 rs)):ts)
  ==. εDB l (updateDB (Pair n' (Table ti rs)    :ts) n p v1 v2)
  *** QED
  | n == n' && tableLabel ti `canFlowTo` l
  =  (Just t' ==. 
      lookupTable n ((Pair n' (Table ti rs)):ts) ==. 
      Just t 
      *** QED)
  &&& (Just εt' ==. 
      lookupTable n (εDB l ((Pair n' (Table ti rs)):ts)) ==. 
      lookupTable n (Pair n' (εTable l (Table ti rs)):εDB l ts) ==. 
      Just (εTable l t) 
      *** QED)
  &&& (εDB l (updateDB (εDB l ((Pair n' t):ts)) n p εv1 εv2)
  ==.  εDB l (updateDB ((Pair n' (εTable l t)):εDB l ts) n p εv1 εv2)
  ==.  εDB l (updateDB ((Pair n' (εTable l (Table ti rs))):εDB l ts) n p εv1 εv2)
  ==.  εDB l (updateDB ((Pair n' (Table ti (εRows l ti rs))):εDB l ts) n p εv1 εv2)
  ==.  εDB l (Pair n' (Table ti (updateRows p εv1 εv2 (εRows l ti rs))):εDB l ts) 
  ==.  Pair n' (εTable l (Table ti (updateRows p εv1 εv2 (εRows l ti rs)))):εDB l (εDB l ts)
  ==.  Pair n' (Table ti (εRows l ti (updateRows p εv1 εv2 (εRows l ti rs)))):εDB l (εDB l ts)
      ? assert (updateLabelCheck lc t p l1 v1 l2 v2)
      ? assert (updateLabelCheck lc εt' p l1 εv1 l2 εv2)
      ? simulationsUpdateRows l lc lφ εlφ ti p l1 v1 l2 v2 rs
      ? assert (εRows l ti (updateRows p εv1 εv2 (εRows l ti rs)) == εRows l ti (updateRows p v1 v2 rs))
      ? εDBIdempotent l ts
  ==. Pair n' (Table ti (εRows l ti (updateRows p v1 v2 rs))):εDB l ts 
  ==. Pair n' (εTable l (Table ti (updateRows p v1 v2 rs))):εDB l ts 
  ==. εDB l (Pair n' (Table ti (updateRows p v1 v2 rs)):ts) 
  ==. εDB l (updateDB (Pair n' (Table ti rs):ts) n p v1 v2)
  *** QED) 

  | n /= n' 
  =  (Just t' ==. 
      lookupTable n ((Pair n' (Table ti rs)):ts) ==. 
      Just t 
      *** QED)
  &&& (Just εt' ==. 
      lookupTable n (εDB l ((Pair n' (Table ti rs)):ts)) ==. 
      lookupTable n (Pair n' (εTable l (Table ti rs)):εDB l ts) ==. 
      Just (εTable l t) 
      *** QED)
  &&& (εDB l (updateDB (εDB l ((Pair n' t):ts)) n p εv1 εv2)
  ==.  εDB l (updateDB ((Pair n' (εTable l t)):εDB l ts) n p εv1 εv2)
  ==.  εDB l (Pair n' (εTable l (Table ti rs)): updateDB (εDB l ts) n p εv1 εv2)
  ==.  Pair n' (εTable l (εTable l (Table ti rs))):εDB l (updateDB (εDB l ts) n p εv1 εv2)
      ? simulationsUpdate l lc ts n p l1 v1 l2 v2 t' εt'
      ? assert (εDB l (updateDB (εDB l ts) n p εv1 εv2) == εDB l (updateDB ts n p v1 v2))
      ? εTableIdempotent l (Table ti rs)
  ==. Pair n' (εTable l (Table ti rs)):εDB l (updateDB ts n p v1 v2)
  ==. εDB l (Pair n' (Table ti rs):updateDB ts n p v1 v2)
  ==. εDB l (updateDB (Pair n' (Table ti rs):ts) n p v1 v2)
  *** QED) 

  where
    εv1 = if (canFlowTo l1 l) then v1 else THole
    εv2 = if (canFlowTo l2 l) then v2 else THole
    lφ  = lawFlowReflexivity (lfRows p ti rs) `cast` lfTable p (Table ti rs)
    εlφ = lawFlowReflexivity (lfRows p ti (εRows l ti rs)) `cast` lfTable p (Table ti (εRows l ti rs))

{-@ simulationsUpdateRows
  :: (Label l, Eq l)
  => l:l -> lc:{l | canFlowTo lc l }
  -> lf:l -> elf:l 
  -> ti:TInfo l 
  -> p:Pred 
  -> l1:l 
  -> v1: SDBTerm l 
  -> l2:l 
  -> v2: SDBTerm l 
  -> rs:{[Row l] | (canFlowTo (lfRows p ti rs) lf) && (canFlowTo (lfRows p ti (εRows l ti rs)) elf) && (updateRowsCheck lc lf ti p l1 v1 l2 v2 rs) && (updateRowsCheck lc elf ti p l1 (if (canFlowTo l1 l) then v1 else THole) l2 (if (canFlowTo l2 l) then v2 else THole) (εRows l ti rs))} 
  -> { (εRows l ti (updateRows p (if (canFlowTo l1 l) then v1 else THole) (if (canFlowTo l2 l) then v2 else THole) (εRows l ti rs)) = εRows l ti (updateRows p v1 v2 rs)) } 
   / [len rs] @-}
simulationsUpdateRows
  :: (Label l, Eq l)
  => l -> l -> l -> l-> TInfo l -> Pred -> l -> Term l -> l -> Term l -> [Row l] -> Proof 
simulationsUpdateRows l lc _ _ ti p l1 v1 l2 v2 [] 
  =   εRows l ti (updateRows p εv1 εv2 (εRows l ti []))
  ==. εRows l ti (updateRows p v1 v2 [])
  *** QED   
  where
    εv1 = if (canFlowTo l1 l) then v1 else THole
    εv2 = if (canFlowTo l2 l) then v2 else THole

simulationsUpdateRows l lc lφ εlφ ti p l1 v1 l2 v2 (r:rs) 
  =   εRows l ti (updateRows p εv1 εv2 (εRows l ti (r:rs)))
  ==. εRows l ti (updateRows p εv1 εv2 (εRow l ti r:εRows l ti rs))
  ==. εRows l ti (updateRow p εv1 εv2 (εRow l ti r):updateRows p εv1 εv2 (εRows l ti rs))
  ==. εRow l ti (updateRow p εv1 εv2 (εRow l ti r)):εRows l ti (updateRows p εv1 εv2 (εRows l ti rs))
      ? assert (updateRowsCheck lc εlφ ti p l1 εv1 l2 εv2 (εRows l ti (r:rs)))
      ? assert (updateRowsCheck lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r:εRows l ti rs))
      ? assert (updateRowCheck lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r))
      ? assert (updateRowsCheck lc εlφ ti p l1 εv1 l2 εv2 (εRows l ti rs))
      ? assert (updateRowsCheck lc lφ ti p l1 v1 l2 v2 (r:rs))
      ? assert (updateRowsCheck lc lφ ti p l1 v1 l2 v2 rs)
      ? assert (updateRowCheck lc lφ ti p l1 v1 l2 v2 r)
      ? assert (lfRows p ti (r:rs) `canFlowTo` lφ)
      ? assert ((lfRow p ti r `join` lfRows p ti rs) `canFlowTo` lφ)
      ? joinCanFlowTo (lfRow p ti r) (lfRows p ti rs) lφ
      ? assert (lfRows p ti (εRows l ti (r:rs)) `canFlowTo` εlφ)
      ? assert (lfRows p ti (εRow l ti r:εRows l ti rs) `canFlowTo` εlφ)
      ? assert ((lfRow p ti (εRow l ti r) `join` lfRows p ti (εRows l ti rs)) `canFlowTo` εlφ)
      ? joinCanFlowTo (lfRow p ti (εRow l ti r)) (lfRows p ti (εRows l ti rs)) εlφ
      ? assert (updateRowCheck lc lφ ti p l1 v1 l2 v2 r)
      ? simulationsUpdateRows l lc lφ εlφ ti p l1 v1 l2 v2 rs
      ? simulationsUpdateRow  l lc lφ εlφ ti p l1 v1 l2 v2 r
  ==. εRow  l ti (updateRow p v1 v2 r):εRows l ti (updateRows p v1 v2 rs)
  ==. εRows l ti (updateRow p v1 v2 r:updateRows p v1 v2 rs)
  ==. εRows l ti (updateRows p v1 v2 (r:rs))
  *** QED  
  where
    εv1 = if (canFlowTo l1 l) then v1 else THole
    εv2 = if (canFlowTo l2 l) then v2 else THole
 


{-@ simulationsUpdateRow 
  :: (Label l, Eq l)
  => l:l -> lc:{l | canFlowTo lc l } -> lf:l -> elf:l
  -> ti:TInfo l 
  -> p:Pred 
  -> l1:l 
  -> v1: SDBTerm l 
  -> l2:l 
  -> v2: SDBTerm l 
  -> r: {Row l | (canFlowTo (lfRow p ti r) lf) && (canFlowTo (lfRow p ti (εRow l ti r)) elf) && (updateRowCheck lc lf ti p l1 v1 l2 v2 r) && (updateRowCheck lc elf ti p l1 (if (canFlowTo l1 l) then v1 else THole) l2 (if (canFlowTo l2 l) then v2 else THole) (εRow l ti r)) } 
  -> { εRow l ti (updateRow p (if (canFlowTo l1 l) then v1 else THole) (if (canFlowTo l2 l) then v2 else THole) (εRow l ti r)) = εRow l ti (updateRow p v1 v2 r) } @-}
simulationsUpdateRow 
  :: (Label l, Eq l)
  => l -> l -> l -> l -> TInfo l -> Pred -> l -> Term l -> l -> Term l -> Row l -> Proof 
simulationsUpdateRow l lc lφ εlφ ti p l1 v1 l2 v2 r@(Row k o1 o2)
  =   εRow l ti (updateRow p εv1 εv2 (εRow l ti (Row k o1 o2))) 
      ? globals
  ==. εRow l ti (updateRow p v1 v2 (Row k o1 o2))
  *** QED 
    where 
      εr  = Row k (εTerm l o1) THole
      εv1 = if (canFlowTo l1 l) then v1 else THole
      εv2 = if (canFlowTo l2 l) then v2 else THole
      εo2 = if makeValLabel ti o1 `canFlowTo` l then (εTerm l v2) else THole
      lφR  = lfRow p ti r  
      lφER = lfRow p ti (εRow l ti r)
      globals =  
          assert (updateRowCheck  lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r))
        ? assert (updateRowLabel1 lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r))
        ? assert (updateRowLabel2 lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r))
        ? assert (updateRowCheck  lc lφ ti p l1 v1 l2 v2 r)
        ? assert (updateRowLabel1 lc lφ ti p l1 v1 l2 v2 r)
        ? assert (updateRowLabel2 lc lφ ti p l1 v1 l2 v2 r)
        ? assert (lφR  `canFlowTo`  lφ)
        ? assert (lφER `canFlowTo` εlφ)
        ? joinCanFlowTo (l1 `join` lc) lφ (field1Label ti)
        ? lawFlowTransitivity lφR  lφ (field1Label ti) 
        ? joinCanFlowTo (l1 `join` lc) εlφ (field1Label ti)
        ? lawFlowTransitivity lφER  εlφ (field1Label ti) 
        ? joinCanFlowTo l1 lc (field1Label ti)
        ? joinCanFlowTo (l2 `join` lc) lφ (makeValLabel ti v1)
        ? lawFlowTransitivity lφR  lφ (makeValLabel ti v1) 
        ? joinCanFlowTo (l2 `join` lc) εlφ (makeValLabel ti v1)
        ? lawFlowTransitivity lφER  εlφ (makeValLabel ti v1) 
        ? joinCanFlowTo l2 lc (makeValLabel ti v1)
        ? joinCanFlowTo (l2 `join` lc)  lφ (makeValLabel ti εv1)
        ? lawFlowTransitivity lφR  lφ (makeValLabel ti εv1) 
        ? joinCanFlowTo (l2 `join` lc) εlφ (makeValLabel ti εv1)
        ? lawFlowTransitivity lφER  εlφ (makeValLabel ti εv1) 
        ? joinCanFlowTo l2 lc (makeValLabel ti εv1)
        ? lawFlowTransitivity l2 (makeValLabel ti o1)  l 
        ? lawFlowTransitivity l2 (makeValLabel ti v1)  l 
        ? lawFlowTransitivity l2 (makeValLabel ti εv1) l 
        ? lawFlowTransitivity l1 (field1Label ti)      l 
        ? lawFlowTransitivity (makeValLabel ti o1) (field1Label ti)      l 
        ? lawFlowTransitivity (makeValLabel ti o1) (makeValLabel ti εv1) l 
        ? lawFlowTransitivity (makeValLabel ti o1) (makeValLabel ti  v1) l 
        ? lawFlowTransitivity (field1Label ti) (makeValLabel ti εv1) l 
        ? lawFlowTransitivity (field1Label ti) (makeValLabel ti  v1) l 
        ? assert (εTerm l THole == THole)
        ? assert (εTerm l v1 == v1 )  
        ? assert (εTerm l v2 == v2 )  
        ? assert (εTerm l o1 == o1 )  
        ? assert (εTerm l o2 == o2 )  
        ? (evalPred p r *** QED )
        ? (evalPred p (εRow l ti r) *** QED )
        ? (evalPred p εr *** QED )

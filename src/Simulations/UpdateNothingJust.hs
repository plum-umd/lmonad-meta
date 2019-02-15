{-@ LIQUID "--reflection"  @-}

module Simulations.UpdateNothingJust  (simulationsUpdateNothingJust) where

import ProofCombinators
import Labels 
import Programs 
import Predicates 

import Idempotence 
import Simulations.Terms 

import Prelude hiding (Maybe(..), fromJust, isJust)
{-@ simulationsUpdateNothingJust
  :: Label l => l:l -> lc:{l | canFlowTo lc l } 
  -> db:DB l 
  -> n:{TName | isJust (lookupTable n db) }
  -> p:Pred
  -> l2:l  
  -> v2:SDBTerm l 
  -> t: {Table l | (Just t == lookupTable n db) && (updateLabelCheckNothingJust lc t p l2 v2)}
  -> εt:{Table l | (Just εt == lookupTable n (εDB l db)) &&
                   (updateLabelCheckNothingJust lc εt p l2 (if (canFlowTo l2 l) then v2 else THole)) } 
  -> { εDB l (updateDBNothingJust (εDB l db) n p (if (canFlowTo l2 l) then v2 else THole)) == εDB l (updateDBNothingJust db n p v2) } @-}

simulationsUpdateNothingJust :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> l -> Term l -> Table l -> Table l  -> Proof
simulationsUpdateNothingJust l lc [] n p l2 v2 _ _
  =   εDB l (updateDBNothingJust [] n p v2) 
  ==. εDB l [] 
  ==. εDB l (updateDBNothingJust (εDB l []) n p εv2) 
  *** QED 
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole

    -- is this file needed at all?
simulationsUpdateNothingJust l lc ((Pair n' t@(Table ti rs)):ts) n p l2 v2 t' εt'
  | n == n' && not (tableLabel ti `canFlowTo` l)
  =   εDB l (updateDBNothingJust (εDB l ((Pair n' t):ts)) n p εv2)
  ==. εDB l (updateDBNothingJust (Pair n' (εTable l t): εDB l ts) n p εv2)
  ==. εDB l (updateDBNothingJust (Pair n' (Table ti []): εDB l ts) n p εv2)
  ==. εDB l (Pair n' (Table ti (updateRowsNothingJust p εv2 [])): εDB l ts)
  ==. εDB l (Pair n' (Table ti []): εDB l ts)
  ==. Pair n' (εTable l (Table ti [])) : εDB l (εDB l ts)
      ? εDBIdempotent l ts
  ==. Pair n' (Table ti []) : εDB l ts
  ==. Pair n' (εTable l (Table ti (updateRowsNothingJust p v2 rs))):εDB l ts
  ==. εDB l (Pair n' (Table ti (updateRowsNothingJust p v2 rs)):ts)
  ==. εDB l (updateDBNothingJust (Pair n' t:ts) n p v2)
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
  &&& (εDB l (updateDBNothingJust (εDB l ((Pair n' t):ts)) n p εv2)
  ==.  εDB l (updateDBNothingJust ((Pair n' (εTable l t)):εDB l ts) n p εv2)
  ==.  εDB l (updateDBNothingJust ((Pair n' (εTable l (Table ti rs))):εDB l ts) n p εv2)
  ==.  εDB l (updateDBNothingJust ((Pair n' (Table ti (εRows l ti rs))):εDB l ts) n p εv2)
  ==.  εDB l (Pair n' (Table ti (updateRowsNothingJust p εv2 (εRows l ti rs))):εDB l ts) 
  ==.  Pair n' (εTable l (Table ti (updateRowsNothingJust p εv2 (εRows l ti rs)))):εDB l (εDB l ts)
  ==.  Pair n' (Table ti (εRows l ti (updateRowsNothingJust p εv2 (εRows l ti rs)))):εDB l (εDB l ts)
      ? assert (updateLabelCheckNothingJust lc t p l2 v2)
      ? assert (updateLabelCheckNothingJust lc εt' p l2 εv2)
      ? simulationsUpdateRowsNothingJust l lc lφ εlφ ti p l2 v2 rs
      ? assert (εRows l ti (updateRowsNothingJust p εv2 (εRows l ti rs)) == εRows l ti (updateRowsNothingJust p v2 rs))
      ? εDBIdempotent l ts
  ==. Pair n' (Table ti (εRows l ti (updateRowsNothingJust p v2 rs))):εDB l ts 
  ==. Pair n' (εTable l (Table ti (updateRowsNothingJust p v2 rs))):εDB l ts 
  ==. εDB l (Pair n' (Table ti (updateRowsNothingJust p v2 rs)):ts) 
  ==. εDB l (updateDBNothingJust (Pair n' (Table ti rs):ts) n p v2)
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
  &&& (εDB l (updateDBNothingJust (εDB l ((Pair n' t):ts)) n p εv2)
  ==.  εDB l (updateDBNothingJust ((Pair n' (εTable l t)):εDB l ts) n p εv2)
  ==.  εDB l (Pair n' (εTable l (Table ti rs)): updateDBNothingJust (εDB l ts) n p εv2)
  ==.  Pair n' (εTable l (εTable l (Table ti rs))):εDB l (updateDBNothingJust (εDB l ts) n p εv2)
      ? simulationsUpdateNothingJust l lc ts n p l2 v2 t' εt'
      ? assert (εDB l (updateDBNothingJust (εDB l ts) n p εv2) == εDB l (updateDBNothingJust ts n p v2))
      ? εTableIdempotent l (Table ti rs)
  ==. Pair n' (εTable l (Table ti rs)):εDB l (updateDBNothingJust ts n p v2)
  ==. εDB l (Pair n' (Table ti rs):updateDBNothingJust ts n p v2)
  ==. εDB l (updateDBNothingJust (Pair n' (Table ti rs):ts) n p v2)
  *** QED) 

  where
    εv2 = if (canFlowTo l2 l) then v2 else THole
    lφ  = lawFlowReflexivity (lfRows p ti rs) `cast` lfTable p (Table ti rs)
    εlφ = lawFlowReflexivity (lfRows p ti (εRows l ti rs)) `cast` lfTable p (Table ti (εRows l ti rs))

{-@ simulationsUpdateRowsNothingJust
  :: (Label l, Eq l)
  => l:l -> lc:{l | canFlowTo lc l }
  -> lf:l -> elf:l 
  -> ti:TInfo l 
  -> p:Pred
  -> l2:l 
  -> v2: SDBTerm l 
  -> rs:{[Row l] | (canFlowTo (lfRows p ti rs) lf) && (canFlowTo (lfRows p ti (εRows l ti rs)) elf) && (updateRowsCheckNothingJust lc lf ti p l2 v2 rs) && (updateRowsCheckNothingJust lc elf ti p l2 (if (canFlowTo l2 l) then v2 else THole) (εRows l ti rs))} 
  -> { (εRows l ti (updateRowsNothingJust p (if (canFlowTo l2 l) then v2 else THole) (εRows l ti rs)) = εRows l ti (updateRowsNothingJust p v2 rs)) } 
   / [len rs] @-}
simulationsUpdateRowsNothingJust
  :: (Label l, Eq l)
  => l -> l -> l -> l-> TInfo l -> Pred -> l -> Term l -> [Row l] -> Proof 
simulationsUpdateRowsNothingJust l lc _ _ ti p l2 v2 [] 
  =   εRows l ti (updateRowsNothingJust p εv2 (εRows l ti []))
  ==. εRows l ti (updateRowsNothingJust p v2 [])
  *** QED   
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole

simulationsUpdateRowsNothingJust l lc lφ εlφ ti p l2 v2 (r:rs) 
  =   εRows l ti (updateRowsNothingJust p εv2 (εRows l ti (r:rs)))
  ==. εRows l ti (updateRowsNothingJust p εv2 (εRow l ti r:εRows l ti rs))
  ==. εRows l ti (updateRowNothingJust p εv2 (εRow l ti r):updateRowsNothingJust p εv2 (εRows l ti rs))
  ==. εRow l ti (updateRowNothingJust p εv2 (εRow l ti r)):εRows l ti (updateRowsNothingJust p εv2 (εRows l ti rs))
      ? assert (updateRowsCheckNothingJust lc εlφ ti p l2 εv2 (εRows l ti (r:rs)))
      ? assert (updateRowsCheckNothingJust lc εlφ ti p l2 εv2 (εRow l ti r:εRows l ti rs))
      ? assert (updateRowCheckNothingJust lc εlφ ti p l2 εv2 (εRow l ti r))
      ? assert (updateRowsCheckNothingJust lc εlφ ti p l2 εv2 (εRows l ti rs))
      ? assert (updateRowsCheckNothingJust lc lφ ti p l2 v2 (r:rs))
      ? assert (updateRowsCheckNothingJust lc lφ ti p l2 v2 rs)
      ? assert (updateRowCheckNothingJust lc lφ ti p l2 v2 r)
      ? assert (lfRows p ti (r:rs) `canFlowTo` lφ)
      ? assert ((lfRow p ti r `join` lfRows p ti rs) `canFlowTo` lφ)
      ? joinCanFlowTo (lfRow p ti r) (lfRows p ti rs) lφ
      ? assert (lfRows p ti (εRows l ti (r:rs)) `canFlowTo` εlφ)
      ? assert (lfRows p ti (εRow l ti r:εRows l ti rs) `canFlowTo` εlφ)
      ? assert ((lfRow p ti (εRow l ti r) `join` lfRows p ti (εRows l ti rs)) `canFlowTo` εlφ)
      ? joinCanFlowTo (lfRow p ti (εRow l ti r)) (lfRows p ti (εRows l ti rs)) εlφ
      ? assert (updateRowCheckNothingJust lc lφ ti p l2 v2 r)
      ? simulationsUpdateRowsNothingJust l lc lφ εlφ ti p l2 v2 rs
      ? simulationsUpdateRowNothingJust  l lc lφ εlφ ti p l2 v2 r
  ==. εRow  l ti (updateRowNothingJust p v2 r):εRows l ti (updateRowsNothingJust p v2 rs)
  ==. εRows l ti (updateRowNothingJust p v2 r:updateRowsNothingJust p v2 rs)
  ==. εRows l ti (updateRowsNothingJust p v2 (r:rs))
  *** QED  
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole


{-@ simulationsUpdateRowNothingJust
  :: (Label l, Eq l)
  => l:l -> lc:{l | canFlowTo lc l } -> lf:l -> elf:l
  -> ti:TInfo l 
  -> p:Pred
  -> l2:l 
  -> v2: SDBTerm l 
  -> r: {Row l | (canFlowTo (lfRow p ti r) lf) && (canFlowTo (lfRow p ti (εRow l ti r)) elf) && (updateRowCheckNothingJust lc lf ti p l2 v2 r) && (updateRowCheckNothingJust lc elf ti p l2 (if (canFlowTo l2 l) then v2 else THole) (εRow l ti r)) } 
  -> { εRow l ti (updateRowNothingJust p (if (canFlowTo l2 l) then v2 else THole) (εRow l ti r)) = εRow l ti (updateRowNothingJust p v2 r) } @-}
simulationsUpdateRowNothingJust
  :: (Label l, Eq l)
  => l -> l -> l -> l -> TInfo l -> Pred -> l -> Term l -> Row l -> Proof 
simulationsUpdateRowNothingJust l lc lφ εlφ ti p l2 v2 r@(Row k o1 o2)
  =   εRow l ti (updateRowNothingJust p εv2 (εRow l ti (Row k o1 o2))) 
      ? globals
  ==. εRow l ti (updateRowNothingJust p v2 (Row k o1 o2))
  *** QED 
    where 
      εr  = Row k (εTerm l o1) THole
      εv2 = if (canFlowTo l2 l) then v2 else THole
      l1 = field1Label ti
      v1 = o1
      εv1 =if (canFlowTo l1 l) then v1 else THole
      εo2 = if makeValLabel ti o1 `canFlowTo` l then (εTerm l v2) else THole
      lφR  = lfRow p ti r  
      lφER = lfRow p ti (εRow l ti r)
      globals =  
          assert (updateRowCheckNothingJust  lc εlφ ti p l2 εv2 (εRow l ti r))
        ? assert (updateRowLabel2 lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r))
        ? assert (updateRowCheckNothingJust  lc lφ ti p l2 v2 r)
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

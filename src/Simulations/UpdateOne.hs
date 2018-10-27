{-@ LIQUID "--reflection"  @-}

module Simulations.UpdateOne where

import ProofCombinators
import Labels 
import Programs 

import Idempotence 
import LabelUpdateCheck 
import Simulations.Terms
import Simulations.UpdateRowBySMT 

import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsUpdateOneErased  
  :: Label l => l:l -> lc:{l | canFlowTo lc l } 
  -> db:DB l 
  -> n:{TName | isJust (lookupTable n db) && isJust (lookupTable n (εDB l db))}
  -> p:Pred
  -> l1:l 
  -> v1:SDBTerm l
  -> l2:l  
  -> v2:SDBTerm l 
  -> t:{Table l  | (not (canFlowTo (field1Label (tableInfo t)) l && canFlowTo l1 l)) && (Just t == lookupTable n db) && not (updateLabelCheck lc t p l1 v1 l2 v2) } 
  -> εt:{Table l | (Just εt == lookupTable n (εDB l db)) && (updateLabelCheck lc εt p l1 (if (canFlowTo l1 l) then v1 else THole) l2 (if (canFlowTo l2 l) then v2 else THole)) } 
  -> { εDB l (updateDB (εDB l db) n p (if (canFlowTo l1 l) then v1 else THole) (if (canFlowTo l2 l) then v2 else THole)) == εDB l db } @-}
simulationsUpdateOneErased :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> l -> Term l -> l -> Term l -> Table l -> Table l -> Proof
simulationsUpdateOneErased l lc [] n p l1 v1 l2 v2 _ _ 
  =   εDB l [] 
  ==. εDB l (updateDB (εDB l []) n p εv1 εv2) 
  *** QED 
  where
    εv1 = if (canFlowTo l1 l) then v1 else THole
    εv2 = if (canFlowTo l2 l) then v2 else THole

simulationsUpdateOneErased l lc ((Pair n' t@(Table ti rs)):ts) n p l1 v1 l2 v2 t' εt'
  | n == n' && not (tableLabel ti `canFlowTo` l)
  =   εDB l (updateDB (εDB l ((Pair n' t):ts)) n p εv1 εv2)
  ==. εDB l (updateDB ((Pair n' (εTable l t)):εDB l ts) n p εv1 εv2)
  ==. εDB l (updateDB ((Pair n' (εTable l (Table ti rs))):εDB l ts) n p εv1 εv2)
  ==. εDB l (updateDB ((Pair n' (Table ti [])):εDB l ts) n p εv1 εv2)
  ==. εDB l (Pair n' (Table ti (updateRows p εv1 εv2 [])):εDB l ts)
  ==. Pair n' (εTable l (Table ti [])):(εDB l (εDB l ts))
      ?  εDBIdempotent l ts 
  ==. Pair n' (Table ti []):εDB l ts 
  ==. Pair n' (εTable l (Table ti rs)):εDB l ts 
  ==. εDB l (Pair n' (Table ti rs):ts) 
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
  &&& ( εt' ==. 
        εTable l (Table ti rs) ==. 
        Table ti (εRows l ti rs) *** QED 
      )
  &&& (εDB l (updateDB (εDB l ((Pair n' t):ts)) n p εv1 εv2)
  ==.  εDB l (updateDB ((Pair n' (εTable l t)):εDB l ts) n p εv1 εv2)
  ==.  εDB l (updateDB ((Pair n' (εTable l (Table ti rs))):εDB l ts) n p εv1 εv2)
  ==.  εDB l (updateDB ((Pair n' (Table ti (εRows l ti rs))):εDB l ts) n p εv1 εv2)
  ==.  εDB l (Pair n' (Table ti (updateRows p εv1 εv2 (εRows l ti rs))):εDB l ts) 
  ==.  Pair n' (εTable l (Table ti (updateRows p εv1 εv2 (εRows l ti rs)))):εDB l (εDB l ts)
  ==.  Pair n' (Table ti (εRows l ti (updateRows p εv1 εv2 (εRows l ti rs)))):εDB l (εDB l ts)
      ? use (not (updateLabelCheck lc t p l1 v1 l2 v2))
      ? use (not (updateRowsCheck lc lφ ti p l1 v1 l2 v2 rs))
      ? use (updateLabelCheck lc εt' p l1 εv1 l2 εv2)
      ? use (updateRowsCheck lc (lfTable p εt') ti p l1 εv1 l2 εv2 (εRows l ti rs))
      ? use (canFlowTo (lfRows p ti (εRows l ti rs)) εlφ)
      ? simulationsUpdateRowsErased l lc lφ εlφ ti p l1 v1 l2 v2 rs
      ? use (εRows l ti (updateRows p εv1 εv2 (εRows l ti rs)) == εRows l ti rs)
      ? εDBIdempotent l ts
  ==. Pair n' (Table ti (εRows l ti rs)):εDB l ts 
  ==. Pair n' (εTable l (Table ti rs)):εDB l ts 
  ==. εDB l (Pair n' (Table ti rs):ts)
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
      ? simulationsUpdateOneErased l lc ts n p l1 v1 l2 v2 t' εt'
      ? use (εDB l (updateDB (εDB l ts) n p εv1 εv2) == εDB l ts)
      ? εTableIdempotent l (Table ti rs)
  ==. Pair n' (εTable l (Table ti rs)):εDB l ts
  ==. εDB l (Pair n' (Table ti rs):ts) 
  *** QED) 

  where
    εv1 = if (canFlowTo l1 l) then v1 else THole
    εv2 = if (canFlowTo l2 l) then v2 else THole
    lφ  = lawFlowReflexivity (lfRows p ti rs) `cast` lfTable p (Table ti rs)
    εlφ = lawFlowReflexivity (lfRows p ti (εRows l ti rs)) `cast` lfTable p (Table ti (εRows l ti rs))

{-@ simulationsUpdateRowsErased
  :: (Label l, Eq l)
  => l:l -> lc:{l | canFlowTo lc l } 
  -> lf:l -> elf:l 
  -> ti:TInfo l 
  -> p:Pred 
  -> l1:{l | not (canFlowTo (field1Label ti) l && canFlowTo l1 l)}
  -> v1: SDBTerm l 
  -> l2:l 
  -> v2: SDBTerm l 
  -> rs: {[Row l] | (canFlowTo (lfRows p ti rs) lf) && (canFlowTo (lfRows p ti (εRows l ti rs)) elf) && (not (updateRowsCheck lc lf ti p l1 v1 l2 v2 rs)) && (updateRowsCheck lc elf ti p l1 (if (canFlowTo l1 l) then v1 else THole) l2 (if (canFlowTo l2 l) then v2 else THole) (εRows l ti rs)) } 
  -> { εRows l ti rs = εRows l ti (updateRows p (if (canFlowTo l1 l) then v1 else THole) (if (canFlowTo l2 l) then v2 else THole) (εRows l ti rs)) } / [len rs] @-}
simulationsUpdateRowsErased 
  :: (Label l, Eq l)
  => l -> l -> l -> l -> TInfo l -> Pred -> l -> Term l -> l -> Term l -> [Row l] -> Proof 
simulationsUpdateRowsErased l lc _ _ ti p l1 v1 l2 v2 []
  =   εRows l ti (updateRows p εv1 εv2 (εRows l ti []))
  ==. εRows l ti []
  *** QED   
  where
    εv1 = if (canFlowTo l1 l) then v1 else THole
    εv2 = if (canFlowTo l2 l) then v2 else THole

simulationsUpdateRowsErased l lc lφ εlφ ti p l1 v1 l2 v2 [r]
  =   εRows l ti (updateRows p εv1 εv2 (εRows l ti [r]))
  ==. εRows l ti (updateRows p εv1 εv2 (εRow l ti r:εRows l ti []))
  ==. εRows l ti (updateRow p εv1 εv2 (εRow l ti r):updateRows p εv1 εv2 [])
  ==. εRow l ti (updateRow p εv1 εv2 (εRow l ti r)):εRows l ti []
      ? use (canFlowTo (lfRows p ti [r]) lφ)
      ? use (lfRows p ti [] == bot)
      ? use (canFlowTo (lfRow p ti r `join` bot) lφ) -- XX
      ? joinCanFlowTo (lfRow p ti r) bot lφ
      ? use (canFlowTo (lfRow p ti r) lφ)
      ? use (canFlowTo (lfRows p ti (εRows l ti [r])) εlφ)
      ? use (canFlowTo (lfRow p ti (εRow l ti r) `join` bot) εlφ) -- XX
      ? joinCanFlowTo (lfRow p ti (εRow l ti r)) bot εlφ
      ? use (canFlowTo (lfRow p ti (εRow l ti r)) εlφ)
      ? use (not (updateRowsCheck lc lφ ti p l1 v1 l2 v2 [r]))
      ? use (updateRowsCheck lc lφ ti p l1 v1 l2 v2 [])
      ? use (not (updateRowCheck lc lφ ti p l1 v1 l2 v2 r))
      ? use (updateRowsCheck lc εlφ ti p l1 εv1 l2 εv2 (εRows l ti [r]))
      ? use (updateRowCheck lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r))
      ? simulationsUpdateRowOneErased l lc lφ εlφ ti p l1 v1 l2 v2 r -- XX
  ==. εRow l ti r:εRows l ti []
  ==. εRows l ti [r]
  *** QED   
  where
    εv1 = if (canFlowTo l1 l) then v1 else THole
    εv2 = if (canFlowTo l2 l) then v2 else THole

simulationsUpdateRowsErased l lc lφ εlφ ti p l1 v1 l2 v2 (r:rs) 
  =   εRows l ti (updateRows p εv1 εv2 (εRows l ti (r:rs)))
  ==. εRows l ti (updateRows p εv1 εv2 (εRow l ti r:εRows l ti rs))
  ==. εRows l ti (updateRow p εv1 εv2 (εRow l ti r):updateRows p εv1 εv2 (εRows l ti rs))
  ==. εRow l ti (updateRow p εv1 εv2 (εRow l ti r)):εRows l ti (updateRows p εv1 εv2 (εRows l ti rs))
      ? use (updateRowsCheck lc εlφ ti p l1 εv1 l2 εv2 (εRows l ti (r:rs)))
      ? use (updateRowsCheck lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r:εRows l ti rs))
      ? use (updateRowCheck lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r))
      ? use (updateRowsCheck lc εlφ ti p l1 εv1 l2 εv2 (εRows l ti rs))
      ? use (not (updateRowsCheck lc lφ ti p l1 v1 l2 v2 (r:rs)))
      ? updateRowsCheckEq lc lφ ti p l1 v1 l2 v2 r rs
      ? use (not (updateRowsCheck lc lφ ti p l1 v1 l2 v2 rs))
      ? use (not (updateRowCheck lc lφ ti p l1 v1 l2 v2 r))
      ? use (lfRows p ti (r:rs) `canFlowTo` lφ)
      ? use ((lfRow p ti r `join` lfRows p ti rs) `canFlowTo` lφ)
      ? joinCanFlowTo (lfRow p ti r) (lfRows p ti rs) lφ
      ? use (lfRows p ti (εRows l ti (r:rs)) `canFlowTo` εlφ)
      ? use (lfRows p ti (εRow l ti r:εRows l ti rs) `canFlowTo` εlφ)
      ? use ((lfRow p ti (εRow l ti r) `join` lfRows p ti (εRows l ti rs)) `canFlowTo` εlφ)
      ? joinCanFlowTo (lfRow p ti (εRow l ti r)) (lfRows p ti (εRows l ti rs)) εlφ
      ? simulationsUpdateRowsErased   l lc lφ εlφ ti p l1 v1 l2 v2 rs
      ? simulationsUpdateRowOneErased l lc lφ εlφ ti p l1 v1 l2 v2 r
  ==. εRow  l ti r:εRows l ti rs
  ==. εRows l ti (r:rs)
  *** QED  
  where
    εv1 = if (canFlowTo l1 l) then v1 else THole
    εv2 = if (canFlowTo l2 l) then v2 else THole



{-@ simulationsUpdateOne  
  :: Label l => l:l -> lc:{l | canFlowTo lc l } 
  -> db:DB l 
  -> n:{TName | isJust (lookupTable n db) && isJust (lookupTable n (εDB l db))}
  -> p:Pred
  -> l1:l 
  -> v1:SDBTerm l
  -> l2:l  
  -> v2:SDBTerm l 
  -> t:{Table l | (not (canFlowTo (field1Label (tableInfo t)) l && canFlowTo l1 l)) && (Just t == lookupTable n db) && (updateLabelCheck lc t p l1 v1 l2 v2)  } 
  -> εt:{Table l | (Just εt == lookupTable n (εDB l db)) && not (updateLabelCheck lc εt p l1 (if (canFlowTo l1 l) then v1 else THole) l2 (if (canFlowTo l2 l) then v2 else THole)) } 
  -> { εDB l db == εDB l (updateDB db n p v1 v2) } @-}
simulationsUpdateOne :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> l -> Term l -> l -> Term l -> Table l -> Table l  -> Proof
simulationsUpdateOne l lc [] n p l1 v1 l2 v2 _ _ 
  =   εDB l [] 
  ==. εDB l (updateDB [] n p v1 v2) 
  *** QED 

simulationsUpdateOne l lc ((Pair n' t@(Table ti rs)):ts) n p l1 v1 l2 v2 t' εt'
  | n == n' && (tableLabel ti `canFlowTo` l)
  =  (Just t' ==. 
      lookupTable n ((Pair n' (Table ti rs)):ts) ==. 
      Just t 
      *** QED)
  &&& (Just εt' ==. 
      lookupTable n (εDB l ((Pair n' (Table ti rs)):ts)) ==. 
      lookupTable n (Pair n' (εTable l (Table ti rs)):εDB l ts) ==. 
      Just (εTable l t) 
      *** QED)
  &&& ( εt' ==. 
        εTable l (Table ti rs) ==. 
        Table ti (εRows l ti rs) *** QED 
      )
  &&& (εDB l (updateDB (Pair n' t:ts) n p v1 v2)
  ==.  εDB l (Pair n' (Table ti (updateRows p v1 v2 rs)):ts) 
  ==.  Pair n' (εTable l (Table ti (updateRows p v1 v2 rs))):εDB l ts
  ==.  Pair n' (Table ti (εRows l ti (updateRows p v1 v2 rs))):εDB l ts
      ? use (updateLabelCheck lc t p l1 v1 l2 v2)
      ? use (updateRowsCheck lc lφ ti p l1 v1 l2 v2 rs)
      ? use (not (updateLabelCheck lc εt' p l1 εv1 l2 εv2))
      ? use (not (updateRowsCheck lc (lfTable p εt') ti p l1 εv1 l2 εv2 (εRows l ti rs)))
      ? use (canFlowTo (lfRows p ti rs) lφ)
      ? use (canFlowTo (lfRows p ti (εRows l ti rs)) εlφ)
      ? simulationsUpdateRows l lc lφ εlφ ti p l1 v1 l2 v2 rs
      ? use (εRows l ti (updateRows p v1 v2 rs) == εRows l ti rs)
  ==. Pair n' (Table ti (εRows l ti rs)):εDB l ts 
  ==. Pair n' (εTable l (Table ti rs)):εDB l ts 
  ==. εDB l (Pair n' (Table ti rs):ts)
  *** QED) 

  | n == n' && not (tableLabel ti `canFlowTo` l)
  =   εDB l (updateDB (Pair n' t:ts) n p v1 v2)
  ==. εDB l (Pair n' (Table ti (updateRows p v1 v2 rs)):ts) 
  ==. Pair n' (εTable l (Table ti (updateRows p v1 v2 rs))):εDB l ts
  ==. Pair n' (Table ti []):εDB l ts 
  ==. Pair n' (εTable l (Table ti rs)):εDB l ts 
  ==. εDB l (Pair n' (Table ti rs):ts)
  *** QED 
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
  &&& (εDB l (updateDB (Pair n' t:ts) n p v1 v2)
  ==.  εDB l (Pair n' (Table ti rs): updateDB ts n p v1 v2)
  ==.  Pair n' (εTable l (Table ti rs)):εDB l (updateDB ts n p v1 v2)
      ? simulationsUpdateOne l lc ts n p l1 v1 l2 v2 t' εt'
      ? use (εDB l (updateDB ts n p v1 v2) == εDB l ts)
  ==. Pair n' (εTable l (Table ti rs)):εDB l ts
  ==. εDB l (Pair n' (Table ti rs):ts) 
  *** QED) 

  where
    lφ  = lawFlowReflexivity (lfRows p ti rs) `cast` lfTable p (Table ti rs)
    εlφ = lawFlowReflexivity (lfRows p ti (εRows l ti rs)) `cast` lfTable p (Table ti (εRows l ti rs))

    εv1 = if (canFlowTo l1 l) then v1 else THole
    εv2 = if (canFlowTo l2 l) then v2 else THole



{-@ simulationsUpdateRows
  :: (Label l, Eq l)
  => l:l -> lc:{l | canFlowTo lc l } 
  -> lf:l -> elf:l 
  -> ti:TInfo l 
  -> p:Pred 
  -> l1:{l | not (canFlowTo (field1Label ti) l && canFlowTo l1 l)}
  -> v1: SDBTerm l 
  -> l2:l 
  -> v2: SDBTerm l 
  -> rs: {[Row l] | (canFlowTo (lfRows p ti rs) lf) && (canFlowTo (lfRows p ti (εRows l ti rs)) elf) && (updateRowsCheck lc lf ti p l1 v1 l2 v2 rs) && (not (updateRowsCheck lc elf ti p l1 (if (canFlowTo l1 l) then v1 else THole) l2 (if (canFlowTo l2 l) then v2 else THole) (εRows l ti rs))) } 
  -> { εRows l ti rs = εRows l ti (updateRows p v1 v2 rs) } / [len rs] @-}
simulationsUpdateRows 
  :: (Label l, Eq l)
  => l -> l -> l -> l -> TInfo l -> Pred -> l -> Term l -> l -> Term l -> [Row l] -> Proof 
simulationsUpdateRows l lc _ _ ti p l1 v1 l2 v2 []
  =   εRows l ti (updateRows p v1 v2 [])
  ==. εRows l ti []
  *** QED   

simulationsUpdateRows l lc lφ εlφ ti p l1 v1 l2 v2 [r]
  =   εRows l ti (updateRows p v1 v2 [r])
  ==. εRows l ti (updateRow p v1 v2 r:updateRows p v1 v2 [])
  ==. εRow l ti (updateRow p v1 v2 r):εRows l ti []
      ? use (canFlowTo (lfRows p ti [r]) lφ)
      ? use (lfRows p ti [] == bot)
      ? use (canFlowTo (lfRow p ti r `join` bot) lφ) -- XX
      ? joinCanFlowTo (lfRow p ti r) bot lφ
      ? assert (canFlowTo (lfRow p ti r) lφ)
      ? assert (canFlowTo (lfRows p ti (εRows l ti [r])) εlφ)
      ? assert (canFlowTo (lfRows p ti (εRow l ti r:εRows l ti [])) εlφ)
      ? assert (canFlowTo (lfRow p ti (εRow l ti r) `join` bot) εlφ) -- XX
      ? joinCanFlowTo (lfRow p ti (εRow l ti r)) bot εlφ
      ? assert (canFlowTo (lfRow p ti (εRow l ti r)) εlφ)
      ? use (updateRowsCheck lc lφ ti p l1 v1 l2 v2 [r])
      ? assert (updateRowCheck lc lφ ti p l1 v1 l2 v2 r)
      ? use (updateRowsCheck lc lφ ti p l1 v1 l2 v2 [])
      ? use (not (updateRowsCheck lc εlφ ti p l1 εv1 l2 εv2 (εRows l ti [r])))
      ? use (not (updateRowsCheck lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r:εRows l ti [])))
      ? use (updateRowsCheck lc εlφ ti p l1 εv1 l2 εv2 [])
      ? assert (not (updateRowCheck lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r)))
      ? simulationsUpdateRowOne l lc lφ εlφ ti p l1 v1 l2 v2 r -- XX
  ==. εRow l ti r:εRows l ti []
  ==. εRows l ti [r]
  *** QED   
  where
    εv1 = if (canFlowTo l1 l) then v1 else THole
    εv2 = if (canFlowTo l2 l) then v2 else THole

simulationsUpdateRows l lc lφ εlφ ti p l1 v1 l2 v2 (r:rs) 
  =   εRows l ti (updateRows p v1 v2 (r:rs))
  ==. εRows l ti (updateRow p v1 v2 r:updateRows p v1 v2 rs)
  ==. εRow l ti (updateRow p v1 v2 r):εRows l ti (updateRows p v1 v2 rs)
      ? use (not (updateRowsCheck lc εlφ ti p l1 εv1 l2 εv2 (εRows l ti (r:rs))))
      ? use (updateRowsCheck lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r:εRows l ti rs))
      ? use (updateRowCheck lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r))
      ? use (0 < length (εRows l ti rs))
      ? updateRowsCheckEq lc εlφ ti p l1 εv1 l2 εv2 (εRow l ti r) (εRows l ti rs)
      ? use (not (updateRowsCheck lc εlφ ti p l1 εv1 l2 εv2 (εRows l ti rs)))
      ? use (updateRowsCheck lc lφ ti p l1 v1 l2 v2 (r:rs))
      ? use (updateRowsCheck lc lφ ti p l1 v1 l2 v2 rs)
      ? use (updateRowCheck lc lφ ti p l1 v1 l2 v2 r)
      ? use (lfRows p ti (r:rs) `canFlowTo` lφ)
      ? use ((lfRow p ti r `join` lfRows p ti rs) `canFlowTo` lφ)
      ? joinCanFlowTo (lfRow p ti r) (lfRows p ti rs) lφ
      ? use (lfRows p ti (εRows l ti (r:rs)) `canFlowTo` εlφ)
      ? use (lfRows p ti (εRow l ti r:εRows l ti rs) `canFlowTo` εlφ)
      ? use ((lfRow p ti (εRow l ti r) `join` lfRows p ti (εRows l ti rs)) `canFlowTo` εlφ)
      ? joinCanFlowTo (lfRow p ti (εRow l ti r)) (lfRows p ti (εRows l ti rs)) εlφ
      ? simulationsUpdateRows   l lc lφ εlφ ti p l1 v1 l2 v2 rs
      ? simulationsUpdateRowOne l lc lφ εlφ ti p l1 v1 l2 v2 r
  ==. εRow  l ti r:εRows l ti rs
  ==. εRows l ti (r:rs)
  *** QED  
  where
    εv1 = if (canFlowTo l1 l) then v1 else THole
    εv2 = if (canFlowTo l2 l) then v2 else THole

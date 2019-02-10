{-@ LIQUID "--reflection"  @-}
{-@ infix :  @-}
module LabelUpdateCheckNothingJust where

import Labels 
import Predicates 
import Prelude hiding (Maybe(..), fromJust, isJust)
import Programs 

import ProofCombinators 


{-@ 
labelUpdateCheckEqNothingJust
  :: (Eq l, Label l)
  => l:l 
  -> lc:{l | canFlowTo lc l }
  -> p:Pred
  -> l2:l
  -> v2:SDBTerm l
  -> t:{Table l | canFlowTo (tableLabel (tableInfo t)) l }
  -> { (canFlowTo (field1Label (tableInfo t))  l) 
  => updateLabelCheckNothingJust lc t p l2 v2 == updateLabelCheckNothingJust lc (εTable l t) p l2 (if (canFlowTo l2 l) then (εTerm l v2) else THole) }
@-}
labelUpdateCheckEq :: (Eq l, Label l) => l -> l -> Pred -> l -> Term l -> Table l -> Proof 
labelUpdateCheckEq l lc p l2 v2 t@(Table ti@(TInfo lt _ lf1 _ _) rs)
   | canFlowTo (tableLabel ti) l && canFlowTo (field1Label (tableInfo t)) l
  =   updateLabelCheckNothingJust lc (εTable l (Table ti rs)) p l2 εv2
  ==. updateLabelCheckNothingJust lc (Table ti (εRows l ti rs)) p l2 εv2
  ==. updateRowsCheckNothingJust lc (lfTable p (Table ti (εRows l ti rs))) ti p l2 εv2 (εRows l ti rs)
      ? (   lfTable p (Table ti (εRows l ti rs))
        ==. lfRows p ti rs 
            ? lfRowsEq l p ti rs 
        ==. lfRows p ti (εRows l ti rs)
        ==. lfTable p (Table ti rs) *** QED ) 
      ? labelUpdateCheckEqRows l lc (lfTable p t) l2 v2 ti rs 
  ==. updateRowsCheckNothingJust (lfTable p (Table ti rs)) lc ti p l2 v2 rs
  ==. updateLabelCheckNothingJust lc (Table ti rs) p l2 v2 
  *** QED 
   | otherwise
   = () 
  where
    εv2 = if (canFlowTo l2 l) then (εTerm l v2) else THole

{-@ 
lfRowsEq 
  :: (Eq l, Label l)
  => l:l 
  -> p:Pred 
  -> ti:{TInfo l | canFlowTo (field1Label ti) l }
  -> rs:[Row l] 
  -> { lfRows p ti rs == lfRows p ti (εRows l ti rs) }
  / [len rs] @-}
lfRowsEq :: (Eq l, Label l) => l -> Pred -> TInfo l -> [Row l] -> Proof 
lfRowsEq l p ti []
  =   lfRows p ti (εRows l ti []) 
  ==. bot 
  ==. lfRows p ti [] 
  *** QED 

lfRowsEq l p ti (r@(Row k o1 o2):rs)
  =   lfRows p ti (εRows l ti (r:rs))
  ==. lfRows p ti (εRow l ti r:εRows l ti rs)
  ==. lfRow p ti (εRow l ti r) `join` lfRows p ti (εRows l ti rs)
      ? assert (canFlowTo (field1Label ti) l)
      ? assert (εTerm l o1 == o1)
      ? assert ((rowField1 r) == (rowField1 (εRow l ti r))) 
      ? lfRowsEq l p ti rs  
  ==. lfRow p ti r `join` lfRows p ti rs
  ==. lfRows p ti (r:rs)
  *** QED 



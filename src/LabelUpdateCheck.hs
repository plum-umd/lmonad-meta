{-@ LIQUID "--reflection"  @-}
{-@ infix :  @-}
module LabelUpdateCheck where

import Labels 
import Prelude hiding (Maybe(..), fromJust, isJust)
import Programs 

import ProofCombinators 


{-@ 
updateRowsCheckEq 
  :: (Eq l, Label l)
  => lc:l 
  -> l:l
  -> ti:TInfo l 
  -> p:Pred l
  -> l1:l
  -> v1:{t:Term l | isDBValue t && ςTerm t } 
  -> l2:l
  -> v2:{t:Term l | isDBValue t && ςTerm t }
  -> r:Row l
  -> rs:{[Row l] | 0 < len rs }
  -> { (updateRowsCheck lc l ti p l1 v1 l2 v2 (r:rs) == updateRowsCheck lc l ti p l1 v1 l2 v2 rs) && 
       (updateRowsCheck lc l ti p l1 v1 l2 v2 (r:rs) == updateRowCheck  lc l ti p l1 v1 l2 v2 r)}
  / [len rs] @-}
updateRowsCheckEq :: (Eq l, Label l) => l -> l -> TInfo l -> Pred l -> l -> Term l -> l -> Term l -> Row l -> [Row l] -> Proof 
updateRowsCheckEq lc lφ ti p l1 v1 l2 v2 r [] = () 
updateRowsCheckEq lc lφ ti p l1 v1 l2 v2 r [r'] 
  =   updateRowsCheck lc lφ ti p l1 v1 l2 v2 (r:[r'])
  ==. ( updateRowCheck lc lφ ti p l1 v1 l2 v2 r && 
        updateRowsCheck lc lφ ti p l1 v1 l2 v2 [r'])
  ==. ( updateRowCheck lc lφ ti p l1 v1 l2 v2 r && 
        updateRowCheck lc lφ ti p l1 v1 l2 v2 r' && 
        updateRowsCheck lc lφ ti p l1 v1 l2 v2 []
        ) ? updateRowCheckSame lc lφ ti p l1 v1 l2 v2 r r' 
  ==. ( updateRowCheck lc lφ ti p l1 v1 l2 v2 r && 
        updateRowCheck lc lφ ti p l1 v1 l2 v2 r')
  *** QED 

updateRowsCheckEq lc lφ ti p l1 v1 l2 v2 r (r':rs) 
  =   updateRowsCheck lc lφ ti p l1 v1 l2 v2 (r:(r':rs))
  ==. ( updateRowCheck lc lφ ti p l1 v1 l2 v2 r && 
        updateRowsCheck lc lφ ti p l1 v1 l2 v2 (r':rs))
  ==. ( updateRowCheck lc lφ ti p l1 v1 l2 v2 r && 
        updateRowCheck lc lφ ti p l1 v1 l2 v2 r' && 
        updateRowsCheck lc lφ ti p l1 v1 l2 v2 rs
        ) 
  ? updateRowCheckSame lc lφ ti p l1 v1 l2 v2 r r' 
  ? updateRowsCheckEq lc lφ ti p l1 v1 l2 v2 r rs 
  *** QED 


{-@ 
updateRowCheckSame 
  :: (Eq l, Label l)
  => lc:l 
  -> l:l
  -> ti:TInfo l 
  -> p:Pred l
  -> l1:l
  -> v1:{t:Term l | isDBValue t && ςTerm t } 
  -> l2:l
  -> v2:{t:Term l | isDBValue t && ςTerm t }
  -> x:Row l
  -> y:Row l
  -> { updateRowCheck lc l ti p l1 v1 l2 v2 x == updateRowCheck lc l ti p l1 v1 l2 v2 y }
@-}
updateRowCheckSame :: (Eq l, Label l) => l -> l -> TInfo l -> Pred l -> l -> Term l -> l -> Term l -> Row l -> Row l -> Proof 
updateRowCheckSame lc lφ ti p l1 v1 l2 v2 x y 
  =   updateRowCheck lc lφ ti p l1 v1 l2 v2 x 
  ==. ((updateRowLabel1 lc lφ ti p l1 v1 l2 v2 x)
   && (updateRowLabel2 lc lφ ti p l1 v1 l2 v2 x))
  ==. (((l1 `join` lc) `join` lφ) `canFlowTo` field1Label ti
   && (((l2 `join` lc) `join` lφ) `canFlowTo` makeValLabel ti v1))
  ==. ((updateRowLabel1 lc lφ ti p l1 v1 l2 v2 y)
   && (updateRowLabel2 lc lφ ti p l1 v1 l2 v2 y))
  ==. updateRowCheck lc lφ ti p l1 v1 l2 v2 y 
  *** QED  




{-@ 
labelUpdateCheckEq 
  :: (Eq l, Label l)
  => l:l 
  -> lc:{l | canFlowTo lc l }
  -> p:Pred l
  -> l1:l
  -> v1:{t:Term l | isDBValue t && ςTerm t } 
  -> l2:l
  -> v2:{t:Term l | isDBValue t && ςTerm t }
  -> t:{Table l | canFlowTo (tableLabel (tableInfo t)) l }
  -> { (canFlowTo (join (field1Label (tableInfo t)) l1) l) 
  => updateLabelCheck lc t p l1 v1 l2 v2 == updateLabelCheck lc (εTable l t) p l1 (if (canFlowTo l1 l) then (εTerm l v1) else THole) l2 (if (canFlowTo l2 l) then (εTerm l v2) else THole) }
@-}
labelUpdateCheckEq :: (Eq l, Label l) => l -> l -> Pred l -> l -> Term l -> l -> Term l -> Table l -> Proof 
labelUpdateCheckEq l lc p l1 v1 l2 v2 t@(Table ti@(TInfo lt _ lf1 _ _) rs)
   | canFlowTo (tableLabel ti) l && canFlowTo (join (field1Label (tableInfo t)) l1) l
  =   updateLabelCheck lc (εTable l (Table ti rs)) p l1 εv1 l2 εv2
  ==. updateLabelCheck lc (Table ti (εRows l ti rs)) p l1 εv1 l2 εv2
  ==. updateRowsCheck lc (lfTable p (Table ti (εRows l ti rs))) ti p l1 εv1 l2 εv2 (εRows l ti rs)
      ? joinCanFlowTo (field1Label (tableInfo t)) l1 l 
      ? (   lfTable p (Table ti (εRows l ti rs))
        ==. lfRows p ti rs 
            ? lfRowsEq l p ti rs 
        ==. lfRows p ti (εRows l ti rs)
        ==. lfTable p (Table ti rs) *** QED ) 
      ? labelUpdateCheckEqRows l lc (lfTable p t) p l1 v1 l2 v2 ti rs 
  ==. updateRowsCheck (lfTable p (Table ti rs)) lc ti p l1 v1 l2 v2 rs
  ==. updateLabelCheck lc (Table ti rs) p l1 v1 l2 v2 
  *** QED 
   | otherwise
   = () 
  where
    εv1 = if (canFlowTo l1 l) then (εTerm l v1) else THole
    εv2 = if (canFlowTo l2 l) then (εTerm l v2) else THole



{-@ 
lfRowsEq 
  :: (Eq l, Label l)
  => l:l 
  -> p:Pred l
  -> ti:{TInfo l | canFlowTo (field1Label ti) l }
  -> rs:[Row l] 
  -> { lfRows p ti rs == lfRows p ti (εRows l ti rs) }
  / [len rs] @-}
lfRowsEq :: (Eq l, Label l) => l -> Pred l -> TInfo l -> [Row l] -> Proof 
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



{-@ 
labelUpdateCheckEqRows 
  :: (Eq l, Label l)
  => l:l 
  -> lc:{l | canFlowTo lc l } -> lf:l 
  -> p:Pred l
  -> l1:l
  -> v1:{t:Term l | isDBValue t && ςTerm t } 
  -> l2:l
  -> v2:{t:Term l | isDBValue t && ςTerm t }
  -> ti:{TInfo l | canFlowTo (join (field1Label ti) l1) l }
  -> rs:[Row l] 
  -> { updateRowsCheck lc lf ti p l1 v1 l2 v2 rs == updateRowsCheck lc lf ti p l1 (if (canFlowTo l1 l) then (εTerm l v1) else THole) l2 (if (canFlowTo l2 l) then (εTerm l v2) else THole) (εRows l ti rs) }
  / [len rs] @-}
labelUpdateCheckEqRows :: (Eq l, Label l) => l -> l -> l -> Pred l -> l -> Term l -> l -> Term l -> TInfo l -> [Row l] -> Proof 
labelUpdateCheckEqRows l lc lφ p l1 v1 l2 v2 ti []
  =   updateRowsCheck lc lφ ti p l1 εv1 l2 εv2 (εRows l ti []) 
  ==. updateRowsCheck lc lφ ti p l1 εv1 l2 εv2 [] 
  ==. True 
  ==. updateRowsCheck lc lφ ti p l1 v1 l2 v2 [] 
  *** QED 
  where
    εv1 = if (canFlowTo l1 l) then (εTerm l v1) else THole
    εv2 = if (canFlowTo l2 l) then (εTerm l v2) else THole

labelUpdateCheckEqRows l lc lφ p l1 v1 l2 v2 ti (r@(Row k o1 o2):rs)
  =   updateRowsCheck lc lφ ti p l1 εv1 l2 εv2 (εRows l ti (r:rs)) 
  ==. updateRowsCheck lc lφ ti p l1 εv1 l2 εv2 (εRow l ti r:εRows l ti rs) 
  ==. (updateRowCheck lc lφ ti p l1 εv1 l2 εv2 (εRow l ti r) 
       && updateRowsCheck lc lφ ti p l1 εv1 l2 εv2 (εRows l ti rs))
  ==. (  updateRowLabel1 lc lφ ti p l1 εv1 l2 εv2 (εRow l ti r) 
      && updateRowLabel2 lc lφ ti p l1 εv1 l2 εv2 (εRow l ti r) 
      && updateRowsCheck lc lφ  ti p l1 εv1 l2 εv2 (εRows l ti rs))
  ==. (   (((l1 `join` lc) `join` lφ) `canFlowTo` field1Label ti) 
      && (((l2 `join` lc) `join` lφ) `canFlowTo` makeValLabel ti εv1) 
      && updateRowsCheck lc lφ ti p l1 εv1 l2 εv2 (εRows l ti rs))
      ? assert (canFlowTo (join (field1Label ti) l1) l)
      ? joinCanFlowTo (field1Label ti) l1 l 
      ? assert (εv1 == v1) 
      ? assert (εTerm l o1 == o1)
      ? assert ((rowField1 r) == (rowField1 (εRow l ti r))) 
  ==. (   (((l1 `join` lc) `join` lφ ) `canFlowTo` field1Label ti) 
      && (((l2 `join` lc) `join` lφ ) `canFlowTo` makeValLabel ti v1) 
      && updateRowsCheck lc lφ ti p l1 εv1 l2 εv2 (εRows l ti rs))
  ==.  (  updateRowLabel1 lc lφ ti p l1 v1 l2 v2 r 
      && updateRowLabel2 lc lφ ti p l1 v1 l2 v2 r 
      && updateRowsCheck lc lφ ti p l1 εv1 l2 εv2 (εRows l ti rs))
      ? labelUpdateCheckEqRows l lc lφ p l1 v1 l2 v2 ti rs
  ==. (updateRowCheck lc lφ ti p l1 v1 l2 v2 r 
      && updateRowsCheck lc lφ ti p l1 v1 l2 v2 rs)
  ==. updateRowsCheck lc lφ ti p l1 v1 l2 v2 (r:rs) 
  *** QED 
  where
    εv1 = if (canFlowTo l1 l) then (εTerm l v1) else THole
    εv2 = if (canFlowTo l2 l) then (εTerm l v2) else THole

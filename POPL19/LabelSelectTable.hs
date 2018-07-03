{-@ LIQUID "--reflection"  @-}
module LabelSelectTable where

import Labels 
import Predicates 
import Prelude hiding (Maybe(..), fromJust, isJust)
import Programs 

import ProofCombinators 
 

labelSelectErase :: (Eq l, Label l) => l -> Pred -> TName -> DB l -> Proof
{-@ labelSelectErase :: Label l => l:l -> p:Pred -> n:TName 
  -> db:{DB l | isJust (lookupTable n db) && isJust (lookupTable n (εDB l db)) && 
    ((canFlowTo (field1Label (tableInfo (fromJust (lookupTable n (εDB l db))))) l) 
  &&  canFlowTo (tableLabel (tableInfo (fromJust (lookupTable n (εDB l db))))) l )} 
  -> { labelSelectTable p (fromJust (lookupTable n db)) ==  labelSelectTable p (fromJust (lookupTable n (εDB l db))) }
 @-} 
labelSelectErase l p n [] 
  = assert (isJust (lookupTable n (εDB l []))) 
labelSelectErase l p n' (Pair n t@(Table ti rs):db)
  | n == n', tableLabel ti `canFlowTo` l
  =   labelSelectTable p (fromJust (lookupTable n' (εDB l (Pair n t:db)))) 
  ==. labelSelectTable p (fromJust (lookupTable n' (Pair n (εTable l t):εDB l db))) 
  ==. labelSelectTable p (fromJust (Just (εTable l t))) 
  ==. labelSelectTable p (εTable l t) 
      ? assert (tableLabel ti `canFlowTo` l)
  ==. labelPredTable p (Table ti (εRows l ti rs)) 
  ==. labelSelectRows p ti (εRows l ti rs)
      ? labelSelectEraseRows l p ti rs 
  ==. labelSelectRows p ti rs 
  ==. labelSelectTable p t 
  ==. labelSelectTable p (fromJust (Just t)) 
  ==. labelSelectTable p (fromJust (lookupTable n' (Pair n t:db)))
  *** QED 
labelSelectErase l p n' (Pair n t@(Table ti rs):db)
  | n == n'
  =   labelPredTable p (fromJust (lookupTable n' (εDB l (Pair n t:db)))) `canFlowTo` l
  ==. labelPredTable p (fromJust (lookupTable n' (Pair n (εTable l t):εDB l db))) `canFlowTo` l
  ==. labelPredTable p (fromJust (Just (εTable l t))) `canFlowTo` l
  ==. labelPredTable p (εTable l t) `canFlowTo` l
  ==. labelPredTable p (Table ti []) `canFlowTo` l
  ==. labelPredRows p ti [] `canFlowTo` l
  ==. (tableLabel ti `join` field1Label ti) `canFlowTo` l
      ? joinCanFlowTo (tableLabel ti) (field1Label ti) l
  ==. False 
  ==. tableLabel ti `canFlowTo` l 
       ? tableLabelDep l p ti rs 
  ==. labelPredRows p ti rs `canFlowTo` l
  ==. labelPredTable p t `canFlowTo` l
  ==. labelPredTable p (fromJust (Just t)) `canFlowTo` l
  ==. labelPredTable p (fromJust (lookupTable n' (Pair n t:db))) `canFlowTo` l
  *** QED 


labelSelectErase l p n' (Pair n t:db)
  =   labelPredTable p (fromJust (lookupTable n' (εDB l (Pair n t:db))))
  ==. labelPredTable p (fromJust (lookupTable n' (Pair n (εTable l t):εDB l db)))
  ==. labelPredTable p (fromJust (lookupTable n' (εDB l db)))       
      ? assert (lookupTable n' db == lookupTable n' (Pair n t:db))
      ? labelSelectErase l p n' db  
  ==. labelPredTable p (fromJust (lookupTable n' db))
  ==. labelPredTable p (fromJust (lookupTable n' (Pair n t:db)))
  *** QED 


labelSelectEraseRows :: (Eq l, Label l) => l -> Pred -> TInfo l -> [Row l] -> Proof
{-@ labelSelectEraseRows :: Label l => l:l -> p:Pred 
  -> ti:{TInfo l | canFlowTo (field1Label ti) l && canFlowTo (tableLabel ti) l }
  -> rs:[Row l]
  -> { labelSelectRows p ti rs ==  labelSelectRows p ti (εRows l ti rs) }
 @-} 
labelSelectEraseRows l p ti [] 
  =   labelSelectRows p ti [] 
  ==. labelSelectRows p ti (εRows l ti [])
  *** QED  
labelSelectEraseRows l p ti (r@(Row k v1 v2):rs) 
  =   labelSelectRows p ti (εRows l ti (r:rs))
  ==. labelSelectRows p ti (εRow l ti r:εRows l ti rs)
  ==. labelSelectRows p ti (Row k v1' v2':εRows l ti rs)
  ==. (tableLabel ti `join` labelPredRow p ti (Row k v1' v2')) 
      `join` labelSelectRows p ti (εRows l ti rs)
      ? labelSelectEraseRows l p ti rs 
      ? (rowField1 (Row k v1' v2') ==. v1' ==. v1 *** QED)
  ==. (tableLabel ti `join` labelPredRow p ti r) 
      `join` labelSelectRows p ti rs 
  ==. labelSelectRows p ti (r:rs) 
  *** QED 
  where
    v1' = εTerm l v1
    v2' = if makeValLabel ti v1 `canFlowTo` l then εTerm l v2 else THole 

labelSelectTableImplies :: (Label l, Eq l) => l -> Pred -> Table l -> Proof 
{-@ labelSelectTableImplies 
  :: Label l 
  => l:l 
  -> p:Pred 
  -> t:Table l
  -> { canFlowTo (labelSelectTable p t) l => 
       (canFlowTo (field1Label (tableInfo t)) l &&  canFlowTo (tableLabel (tableInfo t)) l )} @-}
labelSelectTableImplies l p t@(Table ti rs)
  = tableLabelDep l p ti rs 
  ? assert (labelSelectRows p ti rs == labelSelectTable p t)

tableLabelDep :: (Eq l, Label l) => l -> Pred -> TInfo l -> [Row l] -> Proof 
{-@ tableLabelDep 
  :: (Eq l, Label l) 
  => l:l 
  -> p:Pred 
  -> ti:TInfo l 
  -> rs:[Row l] 
  -> { (canFlowTo (labelSelectRows p ti rs) l) 
     => (canFlowTo (field1Label ti) l && canFlowTo (tableLabel ti) l) } @-}
tableLabelDep l p ti [] 
  =   labelSelectRows p ti [] `canFlowTo` l 
  ==. (tableLabel ti `join` field1Label ti) `canFlowTo` l
      ? joinCanFlowTo (tableLabel ti) (field1Label ti) l 
  *** QED  
tableLabelDep l p ti (r:rs) 
  =   labelSelectRows p ti (r:rs) `canFlowTo` l 
  =>. ((tableLabel ti `join` labelPredRow p ti r) `join` labelSelectRows p ti rs) `canFlowTo` l 
       ? joinCanFlowTo (tableLabel ti) (labelPredRow p ti r) l 
       ? joinCanFlowTo (tableLabel ti `join` labelPredRow p ti r) (labelSelectRows p ti rs) l 
       ? joinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 r)) l 
  *** QED 

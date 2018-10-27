{-@ LIQUID "--reflection"  @-}
module LabelPredErase where

import Labels 
import Prelude hiding (Maybe(..), fromJust, isJust)
import Programs 

import ProofCombinators 
import LabelPredImplies

labelPredErase :: (Eq l, Label l) => l -> Pred -> TName -> DB l -> Proof
{-@ labelPredErase :: Label l => l:l -> p:Pred -> n:TName 
  -> db:{DB l | isJust (lookupTable n db) && isJust (lookupTable n (εDB l db)) } 
  -> { not (canFlowTo (labelPredTable p (fromJust (lookupTable n db))) l) <=> not (canFlowTo (labelPredTable p (fromJust (lookupTable n (εDB l db)))) l) }
 @-}
labelPredErase l p n [] 
  = assert (isJust (lookupTable n (εDB l []))) 
labelPredErase l p n' (Pair n t@(Table ti rs):db)
  | n == n', tableLabel ti `canFlowTo` l
  =   labelPredTable p (fromJust (lookupTable n' (εDB l (Pair n t:db)))) `canFlowTo` l
  ==. labelPredTable p (fromJust (lookupTable n' (Pair n (εTable l t):εDB l db))) `canFlowTo` l
  ==. labelPredTable p (fromJust (Just (εTable l t))) `canFlowTo` l
  ==. labelPredTable p (εTable l t) `canFlowTo` l
      ? assert (tableLabel ti `canFlowTo` l)
  ==. labelPredTable p (Table ti (εRows l ti rs)) `canFlowTo` l
  ==. labelPredRows p ti (εRows l ti rs) `canFlowTo` l
      ? labelPredRowsErase l p ti rs 
  ==. labelPredRows p ti rs `canFlowTo` l
  ==. labelPredTable p t `canFlowTo` l
  ==. labelPredTable p (fromJust (Just t)) `canFlowTo` l
  ==. labelPredTable p (fromJust (lookupTable n' (Pair n t:db))) `canFlowTo` l
  *** QED 
labelPredErase l p n' (Pair n t@(Table ti rs):db)
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


labelPredErase l p n' (Pair n t:db)
  =   labelPredTable p (fromJust (lookupTable n' (εDB l (Pair n t:db))))
  ==. labelPredTable p (fromJust (lookupTable n' (Pair n (εTable l t):εDB l db)))
  ==. labelPredTable p (fromJust (lookupTable n' (εDB l db)))       
      ? assert (lookupTable n' db == lookupTable n' (Pair n t:db))
      ? labelPredErase l p n' db  
  ==. labelPredTable p (fromJust (lookupTable n' db))
  ==. labelPredTable p (fromJust (lookupTable n' (Pair n t:db)))
  *** QED 

labelPredRowsErase :: (Eq l, Label l) => l -> Pred -> TInfo l -> [Row l] -> Proof
{-@ labelPredRowsErase 
  :: Label l 
  => l:l 
  -> p:Pred 
  -> ti:{TInfo l | canFlowTo (tableLabel ti) l } 
  -> rs:[Row l]
  -> { not (canFlowTo (labelPredRows p ti rs) l) <=> not (canFlowTo (labelPredRows p ti (εRows l ti rs)) l) }
 @-}

labelPredRowsErase l p ti rs 
   | not (pDep1 p)      
  =   labelPredRows p ti (εRows l ti rs) `canFlowTo` l 
  ==. tableLabel ti `canFlowTo` l 
  ==. labelPredRows p ti rs `canFlowTo` l 
  *** QED 


labelPredRowsErase l p ti [] 
  =   labelPredRows p ti (εRows l ti []) `canFlowTo` l 
  ==. labelPredRows p ti [] `canFlowTo` l 
  *** QED 


labelPredRowsErase l p ti (r:rs)
  =   labelPredRows p ti (εRows l ti (r:rs)) `canFlowTo` l 
  ==. labelPredRows p ti (εRow l ti r:εRows l ti rs) `canFlowTo` l 
  ==. ((tableLabel ti `join` labelPredRow p ti (εRow l ti r)) `join` labelPredRows p ti (εRows l ti rs)) `canFlowTo` l 
      ? unjoinCanFlowTo (tableLabel ti) (labelPredRow p ti (εRow l ti r)) l 
      ?   joinCanFlowTo (tableLabel ti) (labelPredRow p ti (εRow l ti r)) l 
      ? unjoinCanFlowTo (tableLabel ti `join` labelPredRow p ti (εRow l ti r)) (labelPredRows p ti (εRows l ti rs)) l 
      ?   joinCanFlowTo (tableLabel ti `join` labelPredRow p ti (εRow l ti r)) (labelPredRows p ti (εRows l ti rs)) l 
  ==. (  tableLabel ti         `canFlowTo` l 
    &&
        labelPredRow p ti (εRow l ti r) `canFlowTo` l 
    &&
      labelPredRows p ti (εRows l ti rs) `canFlowTo` l
      )
      ? unjoinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 (εRow l ti r))) l 
      ?   joinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 (εRow l ti r))) l 

  ==. ( tableLabel ti         `canFlowTo` l 
    &&
        (field1Label ti `join` makeValLabel ti (rowField1 (εRow l ti r))) `canFlowTo` l 
    &&
      labelPredRows p ti (εRows l ti rs) `canFlowTo` l
      )
      ? unjoinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 (εRow l ti r))) l 
      ?   joinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 (εRow l ti r))) l 
  ==. ( tableLabel ti         `canFlowTo` l 
    &&
        field1Label ti `canFlowTo` l 
    && 
        makeValLabel ti (rowField1 (εRow l ti r)) `canFlowTo` l 
    &&
      labelPredRows p ti (εRows l ti rs) `canFlowTo` l
      )
      ? labelPredRowsErase l p ti rs
      ? assert (εTerm l  (rowField1 r) == rowField1 r)
  ==. ( tableLabel ti         `canFlowTo` l 
    &&
        field1Label ti `canFlowTo` l 
    && 
        makeValLabel ti (rowField1 r)   `canFlowTo` l 
    &&
      labelPredRows p ti rs `canFlowTo` l
      )
      ? unjoinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 r)) l 
      ?   joinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 r)) l 
  ==. ( tableLabel ti         `canFlowTo` l 
    &&
        (field1Label ti `join` makeValLabel ti (rowField1 r))   `canFlowTo` l 
    &&
      labelPredRows p ti rs `canFlowTo` l
      )
  ==. ( tableLabel ti         `canFlowTo` l 
    &&
        labelPredRow p ti r `canFlowTo` l 
    && 
        labelPredRows p ti rs `canFlowTo` l
      )
      ? unjoinCanFlowTo (tableLabel ti) (labelPredRow p ti r) l 
      ?   joinCanFlowTo (tableLabel ti) (labelPredRow p ti r) l 
      ? unjoinCanFlowTo ((tableLabel ti `join` labelPredRow p ti r)) (labelPredRows p ti rs) l 
      ?   joinCanFlowTo ((tableLabel ti `join` labelPredRow p ti r)) (labelPredRows p ti rs) l 
  ==. ((tableLabel ti `join` labelPredRow p ti r) `join` labelPredRows p ti rs) `canFlowTo` l 
  ==. labelPredRows p ti (r:rs) `canFlowTo` l 
  *** QED 





 

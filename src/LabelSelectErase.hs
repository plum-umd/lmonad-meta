{-@ LIQUID "--reflection"  @-}
module LabelSelectErase where

import Labels 
import Prelude hiding (Maybe(..), fromJust, isJust)
import Programs 

import ProofCombinators 
import LabelSelectTable


labelSelectEraseIff :: (Eq l, Label l) => l -> Pred -> TName -> DB l -> Proof
{-@ labelSelectEraseIff :: Label l => l:l -> p:Pred -> n:TName 
  -> db:{DB l | isJust (lookupTable n db) && isJust (lookupTable n (εDB l db)) }
  -> { canFlowTo (labelSelectTable p (fromJust (lookupTable n db))) l <=> canFlowTo (labelSelectTable p (fromJust (lookupTable n (εDB l db)))) l }
 @-} 
labelSelectEraseIff l p n [] 
  = assert (isJust (lookupTable n (εDB l []))) 
labelSelectEraseIff l p n' (Pair n t@(Table ti rs):db)
  | n == n', tableLabel ti `canFlowTo` l
  =   labelSelectTable p (fromJust (lookupTable n' (εDB l (Pair n t:db)))) `canFlowTo` l
  ==. labelSelectTable p (fromJust (lookupTable n' (Pair n (εTable l t):εDB l db))) `canFlowTo` l
  ==. labelSelectTable p (fromJust (Just (εTable l t))) `canFlowTo` l
  ==. labelSelectTable p (εTable l t) `canFlowTo` l
      ? assert (tableLabel ti `canFlowTo` l)
  ==. labelSelectTable p (Table ti (εRows l ti rs)) `canFlowTo` l
  ==. labelSelectRows p ti (εRows l ti rs) `canFlowTo` l
      ? labelPredRowsErase l p ti rs 
  ==. labelSelectRows p ti rs `canFlowTo` l
  ==. labelSelectTable p t `canFlowTo` l
  ==. labelSelectTable p (fromJust (Just t)) `canFlowTo` l
  ==. labelSelectTable p (fromJust (lookupTable n' (Pair n t:db))) `canFlowTo` l
  *** QED 
labelSelectEraseIff l p n' (Pair n t@(Table ti rs):db)
  | n == n'
  =   labelSelectTable p (fromJust (lookupTable n' (εDB l (Pair n t:db)))) `canFlowTo` l
  ==. labelSelectTable p (fromJust (lookupTable n' (Pair n (εTable l t):εDB l db))) `canFlowTo` l
  ==. labelSelectTable p (fromJust (Just (εTable l t))) `canFlowTo` l
  ==. labelSelectTable p (εTable l t) `canFlowTo` l
  ==. labelSelectTable p (Table ti []) `canFlowTo` l
  ==. labelSelectRows p ti [] `canFlowTo` l
  ==. (tableLabel ti `join` field1Label ti) `canFlowTo` l
      ? joinCanFlowTo (tableLabel ti) (field1Label ti) l
  ==. False 
      ? labelSelectTableImplies l p t
  ==. labelSelectTable p t `canFlowTo` l
  ==. labelSelectTable p (fromJust (Just t)) `canFlowTo` l
  ==. labelSelectTable p (fromJust (lookupTable n' (Pair n t:db))) `canFlowTo` l
  *** QED 


labelSelectEraseIff l p n' (Pair n t:db)
  =   labelSelectTable p (fromJust (lookupTable n' (εDB l (Pair n t:db))))
  ==. labelSelectTable p (fromJust (lookupTable n' (Pair n (εTable l t):εDB l db)))
  ==. labelSelectTable p (fromJust (lookupTable n' (εDB l db)))       
      ? assert (lookupTable n' db == lookupTable n' (Pair n t:db))
      ? labelSelectEraseIff l p n' db  
  ==. labelSelectTable p (fromJust (lookupTable n' db))
  ==. labelSelectTable p (fromJust (lookupTable n' (Pair n t:db)))
  *** QED 

labelPredRowsErase :: (Eq l, Label l) => l -> Pred -> TInfo l -> [Row l] -> Proof
{-@ labelPredRowsErase 
  :: Label l 
  => l:l 
  -> p:Pred 
  -> ti:{TInfo l | canFlowTo (tableLabel ti) l } 
  -> rs:[Row l]
  -> { not (canFlowTo (labelSelectRows p ti rs) l) <=> not (canFlowTo (labelSelectRows p ti (εRows l ti rs)) l) }
 @-}

labelPredRowsErase l p ti [] 
  =   labelSelectRows p ti (εRows l ti []) `canFlowTo` l 
  ==. labelSelectRows p ti [] `canFlowTo` l 
  *** QED 


labelPredRowsErase l p ti (r:rs)
  =   labelSelectRows p ti (εRows l ti (r:rs)) `canFlowTo` l 
  ==. labelSelectRows p ti (εRow l ti r:εRows l ti rs) `canFlowTo` l 
  ==. ((tableLabel ti `join` labelPredRow p ti (εRow l ti r)) `join` labelPredRows p ti (εRows l ti rs)) `canFlowTo` l 
      ?   joinCanFlowTo (tableLabel ti) (labelPredRow p ti (εRow l ti r)) l 
      ?   joinCanFlowTo (tableLabel ti `join` labelPredRow p ti (εRow l ti r)) (labelSelectRows p ti (εRows l ti rs)) l 
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
      labelSelectRows p ti rs `canFlowTo` l
      )
  ==. ( tableLabel ti         `canFlowTo` l 
    &&
        labelPredRow p ti r `canFlowTo` l 
    && 
        labelSelectRows p ti rs `canFlowTo` l
      )
      ?   joinCanFlowTo (tableLabel ti) (labelPredRow p ti r) l 
      ?   joinCanFlowTo ((tableLabel ti `join` labelPredRow p ti r)) (labelSelectRows p ti rs) l 
  ==. ((tableLabel ti `join` labelPredRow p ti r) `join` labelSelectRows p ti rs) `canFlowTo` l 
  ==. labelSelectRows p ti (r:rs) `canFlowTo` l 
  *** QED 





 

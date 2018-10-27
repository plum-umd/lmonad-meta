{-@ LIQUID "--reflection"  @-}
module LabelPredEraseEqual (labelPredEraseEqual) where

import Labels 
import Prelude hiding (Maybe(..), fromJust, isJust)
import Programs 

import ProofCombinators 
import LabelPredImplies
import LookupTableErase 
import qualified LabelPredErase as LPE 


labelPredEraseEqual :: (Eq l, Label l) => l -> Pred l -> TName -> DB l -> Proof
{-@ labelPredEraseEqual :: Label l => l:l -> p:Pred l -> n:TName 
  -> db:{DB l | Programs.isJust (lookupTable n db) && Programs.isJust (lookupTable n (εDB l db)) && 
    (canFlowTo (labelPredTable p (Programs.fromJust (lookupTable n db))) l) } 
  -> { labelPredTable p (Programs.fromJust (lookupTable n db)) ==  labelPredTable p (Programs.fromJust (lookupTable n (εDB l db))) }
 @-} 
labelPredEraseEqual l p n db 
  = assert (isJust t )
  ? assert (isJust εt)
  ? assert (canFlowTo (labelPredTable p (fromJust t)) l)
  ? LPE.labelPredErase l p n db 
  ? assert (canFlowTo (labelPredTable p (fromJust εt)) l)
  ? labelPredTableImplies l p (fromJust εt) 
  ? labelPredErase l p n db
  where 
    t  = lookupTable n db
    εt = lookupTable n (εDB l db)

labelPredErase :: (Eq l, Label l) => l -> Pred l -> TName -> DB l -> Proof
{-@ labelPredErase :: Label l => l:l -> p:Pred l -> n:TName 
  -> db:{DB l | (Programs.isJust (lookupTable n db)) && (Programs.isJust (lookupTable n (εDB l db))) && 
    (  (0 < len (tableRows (Programs.fromJust (lookupTable n (εDB l db)))) && pDep1 p) => canFlowTo (field1Label (tableInfo (Programs.fromJust (lookupTable n (εDB l db))))) l) 
  && (canFlowTo (tableLabel (tableInfo (Programs.fromJust (lookupTable n (εDB l db))))) l) } 
  -> { labelPredTable p (Programs.fromJust (lookupTable n db)) ==  labelPredTable p (Programs.fromJust (lookupTable n (εDB l db))) }
 @-} 
labelPredErase l p n [] 
  = assert (isJust (lookupTable n (εDB l []))) 

labelPredErase l p n' db'@(Pair n t@(Table ti rs):db)
  | n == n', tableLabel ti `canFlowTo` l
  =   labelPredTable p (fromJust (lookupTable n' (εDB l (Pair n t:db)))) 
  ==. labelPredTable p (fromJust (lookupTable n' (Pair n (εTable l t):εDB l db))) 
  ==. labelPredTable p (fromJust (Just (εTable l t))) 
  ==. labelPredTable p (εTable l t) 
      ? assert (tableLabel ti `canFlowTo` l)
  ==. labelPredTable p (Table ti (εRows l ti rs)) 
  ==. labelPredRows p ti (εRows l ti rs)
      ? assert (canFlowTo (tableLabel ti) l)
      ? assert (if (0 < length (tableRows (fromJust (lookupTable n' (εDB l db')))) && pDep1 p) then canFlowTo (field1Label ti) l else True)
      ? assert (if (0 < length (εRows l ti rs) && pDep1 p) then canFlowTo (field1Label ti) l else True)
      ? labelSelectEraseRows l p rs ti
  ==. labelPredRows p ti rs 
  ==. labelPredTable p t 
  ==. labelPredTable p (fromJust (Just t)) 
  ==. labelPredTable p (fromJust (lookupTable n' (Pair n t:db)))
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


labelSelectEraseRows :: (Eq l, Label l) => l -> Pred l -> [Row l] -> TInfo l -> Proof
{-@ labelSelectEraseRows :: Label l => l:l -> p:Pred l
  -> rs:[Row l]
  -> ti:{TInfo l | ((0 < len (εRows l ti rs) && pDep1 p) => canFlowTo (field1Label ti) l) && canFlowTo (tableLabel ti) l }
  -> { labelPredRows p ti rs ==  labelPredRows p ti (εRows l ti rs) }
 @-} 


labelSelectEraseRows l p  rs ti
  | not (pDep1 p)      
  =   labelPredRows p ti rs 
  ==. tableLabel ti
  ==. labelPredRows p ti (εRows l ti rs)
  *** QED  

labelSelectEraseRows l p  [] ti
  =   labelPredRows p ti [] 
  ==. labelPredRows p ti (εRows l ti [])
  *** QED  
labelSelectEraseRows l p  (r@(Row k v1 v2):rs) ti
  =   labelPredRows p ti (εRows l ti (r:rs))
  ==. labelPredRows p ti (εRow l ti r:εRows l ti rs)
  ==. labelPredRows p ti (Row k v1' v2':εRows l ti rs)
  ==. (tableLabel ti `join` labelPredRow p ti (Row k v1' v2')) 
      `join` labelPredRows p ti (εRows l ti rs)
      ? labelSelectEraseRows l p rs ti
      ? (rowField1 (Row k v1' v2') ==. v1' ==. v1 *** QED)
  ==. (tableLabel ti `join` labelPredRow p ti r) 
      `join` labelPredRows p ti rs 
  ==. labelPredRows p ti (r:rs) 
  *** QED 
  where
    v1' = εTerm l v1
    v2' = if makeValLabel ti v1 `canFlowTo` l then εTerm l v2 else THole 



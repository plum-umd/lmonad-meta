{-@ LIQUID "--reflection"  @-}
{-@ infix :  @-}
module LabelPredImplies where

import Labels 
import Predicates 
import Prelude hiding (Maybe(..), fromJust, isJust)
import Programs 

import ProofCombinators 


labelPredTableImplies :: (Label l, Eq l) => l -> Pred -> Table l -> Proof 
{-@ labelPredTableImplies 
  :: Label l 
  => l:l 
  -> p:Pred 
  -> t:Table l
  -> { canFlowTo (labelPredTable p t) l => 
       ( ((0 < len (tableRows t) && pDep1 p )=> canFlowTo (field1Label (tableInfo t)) l) && 
         canFlowTo (tableLabel (tableInfo t)) l )} @-}
labelPredTableImplies l p t@(Table ti [])
  | labelPredTable p t `canFlowTo` l 
  = tableLabelDep l p ti []
 

labelPredTableImplies l p t@(Table ti (r:rs))
  | labelPredTable p t `canFlowTo` l, pDep2 p 
  =   labelPredTable p (Table ti (r:rs)) 
  ==. labelPredRows p ti (r:rs) 
  ==. (tableLabel ti `join` labelPredRow p ti r) `join` labelPredRows p ti rs
  ==. (tableLabel ti `join` (field1Label ti `join` makeValLabel ti (rowField1 r))) `join` labelPredRows p ti rs
  *** QED 
  ? tableLabelDep l p ti rs
  ? joinCanFlowTo (tableLabel ti) (labelPredRow p ti r)  l 
  ? joinCanFlowTo (tableLabel ti `join` labelPredRow p ti r) (labelPredRows p ti rs) l 
  ? joinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 r)) l 

labelPredTableImplies l p t@(Table ti (r:rs))
  | labelPredTable p t `canFlowTo` l 
  =   labelPredTable p (Table ti (r:rs)) 
  ==. labelPredRows p ti (r:rs) 
  ==. (tableLabel ti `join` labelPredRow p ti r) `join` labelPredRows p ti rs
  ==. (tableLabel ti `join` field1Label ti) `join` labelPredRows p ti rs
  *** QED 
  ? tableLabelDep l p ti rs
  ? joinCanFlowTo (tableLabel ti) (field1Label ti) l 
  ? joinCanFlowTo (tableLabel ti `join` field1Label ti) (labelPredRows p ti rs) l 



labelPredTableImplies l p t 
  = () 


tableLabelDep :: (Eq l, Label l) => l -> Pred -> TInfo l -> [Row l] -> Proof 
{-@ tableLabelDep 
  :: (Eq l, Label l) 
  => l:l 
  -> p:Pred 
  -> ti:TInfo l 
  -> rs:[Row l] 
  -> { (canFlowTo (labelPredRows p ti rs) l) => (canFlowTo (tableLabel ti) l) } @-}
tableLabelDep l p ti rs 
  | not (pDep1 p)      
  =   labelPredRows p ti rs `canFlowTo` l 
  ==. tableLabel ti         `canFlowTo` l 
  *** QED  

tableLabelDep l p ti [] 
  =   labelPredRows p ti [] `canFlowTo` l 
  ==. (tableLabel ti `join` field1Label ti) `canFlowTo` l 
      ? joinCanFlowTo (tableLabel ti) (field1Label ti) l 
  *** QED  
tableLabelDep l p ti (r:rs) 
  =   labelPredRows p ti (r:rs) `canFlowTo` l 
  =>. ((tableLabel ti `join` labelPredRow p ti r) `join` labelPredRows p ti rs) `canFlowTo` l 
       ? joinCanFlowTo (tableLabel ti) (labelPredRow p ti r) l 
       ? joinCanFlowTo (tableLabel ti `join` labelPredRow p ti r) (labelPredRows p ti rs) l 
  =>. (tableLabel ti `canFlowTo` l 
      && 
  	  labelPredRow p ti r `canFlowTo` l  
     && 
      labelPredRows p ti rs `canFlowTo` l 
      )
      ? tableLabelDep l p ti rs 
  =>. tableLabel ti         `canFlowTo` l 
  *** QED 

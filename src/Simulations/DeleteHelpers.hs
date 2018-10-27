{-@ LIQUID "--reflection"  @-}
module Simulations.DeleteHelpers where

import Labels 
import Prelude hiding (Maybe(..), fromJust, isJust)
import Programs 

import ProofCombinators 




lookupTableErase :: (Label l, Eq l) => l -> DB l -> TName -> Table l -> Proof 
{-@ lookupTableErase :: (Label l, Eq l) 
  => l:l -> db:DB l -> n:{TName | Programs.isJust (lookupTable n db)} 
  -> t:{Table l | Just t == lookupTable n db }
  -> { lookupTable n (εDB l db) == Just (εTable l t) } @-}
lookupTableErase l [] n t 
  =   lookupTable n (εDB l [])
  ==. lookupTable n []
  ==. Nothing  
  *** QED 

lookupTableErase l (Pair n' t:ts) n t' 
  | n == n' 
  =   lookupTable n (εDB l (Pair n' t:ts)) 
  ==. lookupTable n (Pair n' (εTable l t):εDB l ts)
  ==. Just (εTable l t) 
  ?   assert (lookupTable n (Pair n' t:ts) == Just t)
  ?   assert (t == t')
  *** QED

lookupTableErase l (Pair n' t:ts) n t' 
  =   lookupTable n (εDB l (Pair n' t:ts)) 
  ==. lookupTable n (Pair n' (εTable l t):εDB l ts)
  ==. lookupTable n (εDB l ts)
      ? assert (lookupTable n (Pair n' t:ts) == lookupTable n ts)
      ? lookupTableErase l ts n t' 
  ==. Just (εTable l t') 
  *** QED


{-@ 
labelPredTableErase 
  :: (Label l, Eq l)
  => l:l
  -> p:Pred l
  -> t:Table l
  -> { (canFlowTo (tableLabel (tableInfo t)) l && canFlowTo (labelPredTable p t) (tableLabel (tableInfo t))) 
       => canFlowTo (labelReadTable p (tableInfo t)) l}
  @-}

labelPredTableErase :: (Label l, Eq l) => l -> Pred l -> Table l -> Proof 
labelPredTableErase l p t@(Table ti rs) 
  | canFlowTo (tableLabel ti) l
  , canFlowTo (labelPredTable p t) (tableLabel ti) 
  = readCanFlowToPred p t 
  ? lawFlowTransitivity (labelReadTable p ti) (labelPredTable p t) (tableLabel ti)
  ? lawFlowTransitivity (labelReadTable p ti) (tableLabel ti) l
  | otherwise = ()


{-@ 
readCanFlowToPred 
  :: (Label l, Eq l)
  => p:Pred l
  -> t:Table l
  -> { canFlowTo (labelReadTable p (tableInfo t)) (labelPredTable p t)}
  / [len (tableRows t)]
  @-}

readCanFlowToPred :: (Label l, Eq l) => Pred l -> Table l -> Proof 
readCanFlowToPred p t@(Table ti rs) | not (pDep1 p)      
  =   labelPredTable p t
  ==. labelPredRows p ti rs
  ==. tableLabel ti 
      ? assert (labelReadTable p (tableInfo t) == tableLabel ti)
      ? lawFlowReflexivity (tableLabel ti)
  *** QED 

readCanFlowToPred p t@(Table ti []) 
  =   labelPredTable p t
  ==. labelPredRows p ti []
  ==. tableLabel ti `join` field1Label ti
      ? assert (labelReadTable p (tableInfo t) == tableLabel ti `join` field1Label ti)
      ? lawFlowReflexivity (tableLabel ti `join` field1Label ti)
  *** QED 

readCanFlowToPred p t@(Table ti (r:rs)) 
  =   labelPredTable p t
  ==. labelPredRows p ti (r:rs) 
  ==. (tableLabel ti `join` labelPredRow p ti r) `join` labelPredRows p ti rs
  ==. (tableLabel ti 
            `join` (if pDep2 p then field1Label ti `join` makeValLabel ti (rowField1 r) else field1Label ti)
            ) 
            `join` labelPredRows p ti rs
      ? assert (labelReadTable p (tableInfo t) == tableLabel ti `join` field1Label ti)
      ? unjoinCanFlowToItself (tableLabel ti `join` labelPredRow p ti r) (labelPredRows p ti rs)
      ? unjoinCanFlowToItself (tableLabel ti) (labelPredRow p ti r) 
      ? unjoinCanFlowToItself (field1Label ti) (makeValLabel ti (rowField1 r)) 

      ? lawFlowTransitivity (tableLabel ti) (tableLabel ti `join` labelPredRow p ti r) (labelPredTable p t)
      ? lawFlowTransitivity (field1Label ti) (labelPredRow p ti r) (tableLabel ti `join` labelPredRow p ti r)
      ? lawFlowTransitivity (field1Label ti) (tableLabel ti `join` labelPredRow p ti r) (labelPredTable p t)


      ? assert (tableLabel ti `canFlowTo` labelPredTable p t)
      ? assert (field1Label ti `canFlowTo` labelPredTable p t)
      ? joinCanFlowTo (tableLabel ti) (field1Label ti) (labelPredTable p t)

  *** QED 



{-@ 
labelReadFlowsToTableLabel 
  :: (Label l, Eq l)
  => l:l
  -> p:Pred l
  -> ti:TInfo l
  -> { canFlowTo (labelReadTable p ti) l => canFlowTo (tableLabel ti) l }
  @-}

labelReadFlowsToTableLabel :: (Label l, Eq l) => l -> Pred l -> TInfo l -> Proof 
labelReadFlowsToTableLabel l p ti 
  =   labelReadTable p ti 
  ==. (if not (pDep1 p) then tableLabel ti else (tableLabel ti `join` field1Label ti))
      ? joinCanFlowTo (tableLabel ti) (field1Label ti) l 
  *** QED 



{-@ 
labelPredTableEraseEq 
  :: (Label l, Eq l)
  => l:l
  -> p:Pred l
  -> t:{Table l | canFlowTo (labelReadTable p (tableInfo t)) l }
  -> { labelPredTable p t == labelPredTable p (εTable l t) }
  @-}

labelPredTableEraseEq :: (Label l, Eq l) => l -> Pred l -> Table l -> Proof 

labelPredTableEraseEq l p (Table ti r)
  | not (tableLabel ti `canFlowTo` l)
   = assert (tableLabel ti `canFlowTo` labelReadTable p ti 
             ? joinCanFlowTo (tableLabel ti) (field1Label ti) l) 
   ? lawFlowTransitivity (tableLabel ti) (labelReadTable p ti) l 
   ? assert False 

labelPredTableEraseEq l p (Table ti r)
  =   labelPredTable p (εTable l (Table ti r)) 
  ==. labelPredTable p (Table ti (εRows l ti r)) 
  ==. labelPredRows p ti (εRows l ti r) 
      ? assert (canFlowTo (labelReadTable p ti) l)
      ? joinCanFlowTo (tableLabel ti) (field1Label ti) l 
      ? assert (if ((0 < length r) && pDep1 p) then canFlowTo (field1Label ti) l else True)
      ? labelPredRowsErase l p ti r 
  ==. labelPredRows p ti  r 
  ==. labelPredTable p (Table ti r) 
  *** QED 

{-@ 
labelPredRowsErase 
  :: (Label l, Eq l)
  => l:l
  -> p:Pred l
  -> ti: TInfo l
  -> rs: {[Row l] | ((0 < len rs) && pDep1 p )=> (canFlowTo (field1Label ti) l)}
  -> { labelPredRows p ti rs == labelPredRows p ti (εRows l ti rs) }
  @-}

labelPredRowsErase :: (Label l, Eq l) => l -> Pred l -> TInfo l -> [Row l] -> Proof 
labelPredRowsErase l p ti [] 
  =   labelPredRows p ti [] 
  ==. labelPredRows p ti (εRows l ti []) 
  *** QED 

labelPredRowsErase l p ti rs 
  | not (pDep1 p)  
  =   labelPredRows p ti rs  
  ==. tableLabel ti
  ==. labelPredRows p ti (εRows l ti rs) 
  *** QED 

labelPredRowsErase l p ti (r@(Row k v1 v2):rs) 
  =   labelPredRows p ti (r:rs) 
  ==. labelPredRow p ti r             `join` labelPredRows p ti rs 
      ? labelPredRowsErase l p ti rs 
      ? labelPredRowErase l p ti r 
  ==. labelPredRow p ti (εRow l ti r) `join` labelPredRows p ti (εRows l ti rs)  
  ==. labelPredRows p ti (εRow l ti r:εRows l ti rs) 
  ==. labelPredRows p ti (εRows l ti (r:rs)) 
  *** QED 


{-@ 
labelPredRowErase 
  :: (Label l, Eq l)
  => l:l
  -> p:Pred l
  -> ti: {TInfo l | canFlowTo (field1Label ti) l }
  -> r: Row l 
  -> { labelPredRow p ti r == labelPredRow p ti (εRow l ti r) }
  @-}

labelPredRowErase :: (Label l, Eq l) => l -> Pred l -> TInfo l -> Row l -> Proof 
labelPredRowErase l p ti r@(Row k v1 v2) 
  | not (canFlowTo (field1Label ti) l)
  = ()

labelPredRowErase l p ti r@(Row k v1 v2) 
  =   labelPredRow p ti (εRow l ti r)
  ==. labelPredRow p ti r'
  ==. field1Label ti `join` makeValLabel ti v1 
  ==. labelPredRow p ti r 
  *** QED 
  where
    r' = Row k (εTerm l v1) (if makeValLabel ti v1 `canFlowTo` l then (εTerm l v2)  else THole)


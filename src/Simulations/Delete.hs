{-@ LIQUID "--reflection"  @-}
{-@ infix :  @-}

module Simulations.Delete where

import ProofCombinators
import Labels 
import Programs 

import Idempotence 

import LabelPredImplies
import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsDelete  
  :: Label l => l:l 
  -> db:DB l 
  -> n:TName
  -> p:Pred l
  -> t:{Table l | canFlowTo (labelPredTable p t) l && Just t == lookupTable n db} 
  -> { εDB l (deleteDB (εDB l db) n p) == εDB l (deleteDB db n p) } 
  @-}
simulationsDelete :: (Label l, Eq l) 
  => l -> DB l -> TName -> Pred l -> Table l  -> Proof

simulationsDelete l [] n p _ 
  =   εDB l (deleteDB (εDB l []) n p) 
  ==. εDB l (deleteDB [] n p) 
  *** QED 


simulationsDelete l ((Pair n' t@(Table ti rs)):ts) n p _ 
  | n == n', not (tableLabel ti `canFlowTo` l)  
  =   εDB l (deleteDB (εDB l ((Pair n' t):ts)) n p) 
  ==. εDB l (deleteDB (Pair n' (εTable l t):εDB l ts) n p) 
  ==. εDB l (deleteDB (Pair n' (Table ti []):εDB l ts) n p) 
  ==. εDB l (Pair n' (Table ti (deleteRaws p [])):εDB l ts) 
  ==. εDB l (Pair n' (Table ti []):εDB l ts) 
  ==. Pair n' (εTable l (Table ti [])) :εDB l (εDB l ts) 
  ==. Pair n' (Table ti [])            :εDB l (εDB l ts) 
       ? εDBIdempotent l ts 
  ==. Pair n' (Table ti []):εDB l ts 
  ==. Pair n' (εTable l (Table ti (deleteRaws p rs))):εDB l ts 
  ==. εDB l (Pair n' (Table ti (deleteRaws p rs)):ts) 
  ==. εDB l (deleteDB ((Pair n' t):ts) n p) 
  *** QED 


simulationsDelete l ((Pair n' t@(Table ti rs)):ts) n p _ 
  | n == n', labelPredTable p t `canFlowTo` l
  =   εDB l (deleteDB (εDB l ((Pair n' t):ts)) n p) 
  ==. εDB l (deleteDB (Pair n' (εTable l t):εDB l ts) n p) 
  ==. εDB l (deleteDB (Pair n' (Table ti (εRows l ti rs)):εDB l ts) n p) 
  ==. εDB l (Pair n' (Table ti (deleteRaws p (εRows l ti rs))):εDB l ts) 
  ==. Pair n' (εTable l (Table ti (deleteRaws p (εRows l ti rs)))):εDB l (εDB l ts) 
       ? simulationsDeleteRows l p ti rs &&& εDBIdempotent l ts 
  ==. Pair n' (εTable l (Table ti (deleteRaws p rs))):(εDB l ts) 
  ==. εDB l (Pair n' (Table ti (deleteRaws p rs)):ts) 
  ==. εDB l (deleteDB ((Pair n' t):ts) n p) 
  *** QED 


simulationsDelete l (Pair n' t':ts) n p t 
  | n == n'
  =   Just t
  ==. lookupTable n (Pair n' t':ts)
  ==. Just t'
      ? assert (t == t')
  *** QED 


simulationsDelete l ((Pair n' t@(Table ti rs)):ts) n p ti' 
  =   εDB l (deleteDB (εDB l (Pair n' t:ts)) n p) 
  ==. εDB l (deleteDB (Pair n' (εTable l t):εDB l ts) n p) 
  ==. εDB l (Pair n' (εTable l t):deleteDB (εDB l ts) n p) 
  ==. Pair n' (εTable l (εTable l t)):(εDB l (deleteDB (εDB l ts) n p))
       ? (    lookupTableInfo n (Pair n' (Table ti rs):ts)
          ==. case lookupTable n (Pair n' (Table ti rs):ts) of 
                Nothing -> Nothing
                Just (Table ti _) -> Just ti 
          ==. case lookupTable n ts of 
                Nothing -> Nothing
                Just (Table ti _) -> Just ti 
          ==. lookupTableInfo n ts
          *** QED 
         ) &&& assert (lookupTableInfo n (Pair n' (Table ti rs):ts) == lookupTableInfo n ts)
           &&& simulationsDelete l ts n p ti' 
           &&& εTableIdempotent l t 
  ==. Pair n' (εTable l t):(εDB l (deleteDB ts n p))
  ==. εDB l (Pair n' t:deleteDB ts n p) 
  ==. εDB l (deleteDB (Pair n' t:ts) n p) 
  *** QED 

simulationsDeleteRows :: (Eq l, Label l) => l -> Pred l -> TInfo l -> [Row l] -> Proof 
{-@ simulationsDeleteRows 
  :: (Eq l, Label l) 
  => l:l 
  -> p:Pred l
  -> ti:TInfo l
  -> rs:{ [Row l] | canFlowTo (labelPredTable p (Table ti rs)) l } 
  -> { εRows l ti (deleteRaws p (εRows l ti rs)) == εRows l ti (deleteRaws p rs) } @-}

simulationsDeleteRows l p ti rs 
  = undefined 
{- 
simulationsDeleteRows l p ti rs 
  | not (tableLabel ti `canFlowTo` l)
  = labelPredTableImplies l p (Table ti rs)


simulationsDeleteRows l p ti  [] 
  =   εRows l ti (deleteRaws p (εRows l ti []))
  ==. εRows l ti (deleteRaws p [])
  *** QED 


simulationsDeleteRows l p ti (r:rs) 
  | not (pDep1 p), evalPred p r
  =   εRows l ti (deleteRaws p (εRows l ti (r:rs)))
  ==. εRows l ti (deleteRaws p (εRow l ti r:εRows l ti rs))
      ? assert (evalPred p r == pVal p) 
      ? assert (evalPred p (εRow l ti r) == pVal p)
  ==. εRows l ti (deleteRaws p (εRows l ti rs))
      ? recursiveCall l ti p r rs 
      ? simulationsDeleteRows l p ti rs 
  ==. εRows l ti (deleteRaws p rs)
  ==. εRows l ti (deleteRaws p (r:rs))
  *** QED 

simulationsDeleteRows l p ti (r:rs) 
  | not (pDep1 p)
  =   εRows l ti (deleteRaws p (εRows l ti (r:rs)))
  ==. εRows l ti (deleteRaws p (εRow l ti r:εRows l ti rs))
      ? assert (evalPred p r == pVal p) 
      ? assert (evalPred p (εRow l ti r) == pVal p)
  ==. εRows l ti (εRow l ti r:deleteRaws p (εRows l ti rs))
  ==. εRow l ti (εRow l ti r):εRows l ti (deleteRaws p (εRows l ti rs))
      ? recursiveCall l ti p r rs 
      ? simulationsDeleteRows l p ti rs &&& εRowIdempotent l ti r 
  ==. εRow l ti r:εRows l ti (deleteRaws p rs)
  ==. εRows l ti (r:deleteRaws p rs)
  ==. εRows l ti (deleteRaws p (r:rs))
  *** QED 

simulationsDeleteRows l p ti (r@(Row k v1 v2):rs) 
  | evalPred p r, pDep2 p 
  =   εRows l ti (deleteRaws p (εRows l ti (r:rs)))
  ==. εRows l ti (deleteRaws p (εRow l ti r:εRows l ti rs))
       ? assert (εTerm l v1 == v1)
       ? assert (εTerm l v2 == v2)
       ? (    evalPred p (εRow l ti r) 
          ==. p (rowField1 (εRow l ti r)) (rowField2 (εRow l ti r))
          ==. p (rowField1 (εRow l ti (Row k v1 v2))) (rowField2 (εRow l ti (Row k v1 v2)))
          ==. p (rowField1 (Row k (εTerm l v1) (εTerm l v2))) (rowField2 (εRow l ti (Row k v1 v2)))
          ==. p (εTerm l v1) (εTerm l v1)
          ==. evalPred p r
          *** QED)
       ? (    labelPredTable p (Table ti (r:rs))
          ==. labelPredRows p ti (r:rs)
          ==. (tableLabel ti `join` labelPredRow p ti r) `join` labelPredRows p ti rs
          ==. (tableLabel ti `join` (field1Label ti `join` makeValLabel ti (rowField1 r))) `join` labelPredRows p ti rs
          ? joinCanFlowTo (tableLabel ti `join` labelPredRow p ti r) (labelPredRows p ti rs) l 
          ? joinCanFlowTo (tableLabel ti) (labelPredRow p ti r)  l 
          ? joinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 r))  l 
          *** QED
         ) 
  ==. εRows l ti (deleteRaws p (r:εRows l ti rs))
  ==. εRows l ti (deleteRaws p (εRows l ti rs))
      ? recursiveCall l ti p r rs 
      ? assert (labelPredTable p (Table ti rs) `canFlowTo` l)
      ? simulationsDeleteRows l p ti rs
  ==. εRows l ti (deleteRaws p rs)
  ==. εRows l ti (deleteRaws p (r:rs))
  *** QED 


simulationsDeleteRows l p ti (r@(Row k v1 v2):rs) 
  | pDep2 p 
  =   εRows l ti (deleteRaws p (εRows l ti (r:rs)))
  ==. εRows l ti (deleteRaws p (εRow l ti r:εRows l ti rs))
       ? assert (εTerm l v1 == v1)
       ? assert (εTerm l v2 == v2)
       ? (    evalPred p (εRow l ti r) 
          ==. evalPredicate p (Pair (εTerm l v1) (εTerm l v2))
          ==. evalPredicate p (Pair v1 v2)
          ==. evalPred p r
          *** QED)
       ? (    labelPredTable p (Table ti (r:rs))
          ==. labelPredRows p ti (r:rs)
          ==. (tableLabel ti `join` labelPredRow p ti r) `join` labelPredRows p ti rs
          ==. (tableLabel ti `join` (field1Label ti `join` makeValLabel ti (rowField1 r))) `join` labelPredRows p ti rs
          ? joinCanFlowTo (tableLabel ti `join` labelPredRow p ti r) (labelPredRows p ti rs) l 
          ? joinCanFlowTo (tableLabel ti) (labelPredRow p ti r)  l 
          ? joinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 r))  l 
          *** QED
         )  
  ==. εRows l ti (deleteRaws p (r:εRows l ti rs))
  ==. εRows l ti (r:deleteRaws p (εRows l ti rs))
  ==. εRow l ti r:εRows l ti (deleteRaws p (εRows l ti rs))
      ? recursiveCall l ti p r rs 
      ? assert (labelPredTable p (Table ti rs) `canFlowTo` l)
      ? simulationsDeleteRows l p ti rs 
  ==. εRow l ti r:εRows l ti (deleteRaws p rs)
  ==. εRows l ti (r:deleteRaws p rs)
  ==. εRows l ti (deleteRaws p (r:rs))
  *** QED 


simulationsDeleteRows l p ti (r@(Row k v1 v2):rs) 
  | evalPred p r 
  =   εRows l ti (deleteRaws p (εRows l ti (r:rs)))
  ==. εRows l ti (deleteRaws p (εRow l ti r:εRows l ti rs))
       ? (    labelPredTable p (Table ti (r:rs))
          ==. labelPredRows p ti (r:rs)
          ==. (tableLabel ti `join` labelPredRow p ti r) `join` labelPredRows p ti rs
          ==. (tableLabel ti `join` field1Label ti) `join` labelPredRows p ti rs
          ? joinCanFlowTo (tableLabel ti `join` field1Label ti) (labelPredRows p ti rs) l 
          ? joinCanFlowTo (tableLabel ti) (field1Label ti)  l 
          *** QED
         )  
       ? assert (evalPred p r == if pDep1 p then evalPredicate p v1 else pVal p)
       ? assert (evalPred p r == if pDep1 p then evalPredicate p v1 else pVal p)
       ? assert (εTerm l v1 == v1)
       ? assert (evalPred p (εRow l ti r) == evalPred p r)
  ==. εRows l ti (deleteRaws p (r:εRows l ti rs))
  ==. εRows l ti (deleteRaws p (εRows l ti rs))
       ? recursiveCall l ti p r rs 
       ? assert (labelPredTable p (Table ti rs) `canFlowTo` l)
       ? simulationsDeleteRows l p ti rs
  ==. εRows l ti (deleteRaws p rs)
  ==. εRows l ti (deleteRaws p (r:rs))
  *** QED 

simulationsDeleteRows l p ti (r@(Row k v1 v2):rs) 
  =   εRows l ti (deleteRaws p (εRows l ti (r:rs)))
  ==. εRows l ti (deleteRaws p (εRow l ti r:εRows l ti rs))
      ? assert (canFlowTo (labelPredTable p (Table ti (r:rs))) l)
       ? (    labelPredTable p (Table ti (r:rs))
          ==. labelPredRows p ti (r:rs)
          ==. (tableLabel ti `join` labelPredRow p ti r) `join` labelPredRows p ti rs
          ==. (tableLabel ti `join` field1Label ti) `join` labelPredRows p ti rs
          ? joinCanFlowTo (tableLabel ti `join` field1Label ti) (labelPredRows p ti rs) l 
          ? joinCanFlowTo (tableLabel ti) (field1Label ti)  l 
          *** QED
         )  
       ? assert (εTerm l v1 == v1)
       ? assert (evalPred p r == if pDep1 p then evalPredicate p v1 else pVal p)
       ? assert (evalPred p (εRow l ti r) == evalPred p r)
  ==. εRows l ti (deleteRaws p (εRow l ti r:εRows l ti rs))
  ==. εRows l ti (εRow l ti r:deleteRaws p (εRows l ti rs))
  ==. εRow l ti (εRow l ti r):εRows l ti (deleteRaws p (εRows l ti rs))
      ? recursiveCall l ti p r rs 
      ? assert (labelPredTable p (Table ti rs) `canFlowTo` l)
      ? simulationsDeleteRows l p ti rs 
      ? εRowIdempotent l ti r 
  ==. εRow l ti r:εRows l ti (deleteRaws p rs)
  ==. εRows l ti (r:deleteRaws p rs)
  ==. εRows l ti (deleteRaws p (r:rs))
  *** QED 

-}

recursiveCall :: (Eq l, Label l) => l -> TInfo l -> Pred l -> Row l -> [Row l] -> Proof  
{-@ recursiveCall :: (Eq l, Label l) => l:l -> ti:TInfo l -> p:Pred l -> r:Row l -> rs:[Row l] -> 
  {canFlowTo (labelPredTable p (Table ti (r:rs))) l  => canFlowTo (labelPredTable p (Table ti rs)) l } @-}   
recursiveCall l ti p r rs
  =  recursiveCallTrans ti p r rs &&& 
     lawFlowTransitivity (labelPredTable p (Table ti rs)) (labelPredTable p (Table ti (r:rs))) l


recursiveCallTrans :: (Eq l, Label l) => TInfo l -> Pred l -> Row l -> [Row l] -> Proof  
{-@ recursiveCallTrans :: (Eq l, Label l) => ti:TInfo l -> p:Pred l -> r:Row l -> rs:[Row l] -> 
  {canFlowTo (labelPredTable p (Table ti rs)) (labelPredTable p (Table ti (r:rs)))} @-}   
recursiveCallTrans ti p r rs 
  | not (pDep1 p)
  =   labelPredTable p (Table ti (r:rs))
  ==. labelPredRows p ti (r:rs)
  ==. tableLabel ti
  ==. labelPredRows p ti rs
  ==. labelPredTable p (Table ti rs)
      ? lawFlowReflexivity (labelPredTable p (Table ti rs))
  *** QED 

recursiveCallTrans ti p r rs 
  =   labelPredTable p (Table ti (r:rs))
  ==. labelPredRows p ti (r:rs) 
  ==. (tableLabel ti `join` labelPredRow p ti r) `join` labelPredRows p ti rs
  ==. (tableLabel ti `join` labelPredRow p ti r) `join` labelPredTable p (Table ti rs)
      ? unjoinCanFlowToItself (tableLabel ti `join` labelPredRow p ti r) (labelPredTable p (Table ti rs))
  *** QED 


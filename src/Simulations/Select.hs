{-@ LIQUID "--reflection"  @-}
{-@ infix :  @-}

module Simulations.Select where

import ProofCombinators
import Labels 
import Programs 

import Idempotence 
import LabelSelectTable

import Simulations.Terms 
import Simulations.Predicates 

import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsSelect  
  :: Label l 
  => l:l 
  -> db:DB l 
  -> n:TName
  -> p:Pred
  -> t:{Table l | (Just t == lookupTable n db) && (canFlowTo (labelSelectTable p t) l)} 
  -> { εTerm l (selectDB (εDB l db) n p) == εTerm l (selectDB db n p) } 
  @-}
simulationsSelect :: (Label l, Eq l) 
  => l -> DB l -> TName -> Pred -> Table l -> Proof
simulationsSelect l [] n p _
  =   εTerm l (selectDB (εDB l []) n p) 
  ==. εTerm l (selectDB [] n p)
  *** QED 

simulationsSelect l ((Pair n' (Table tinfo rs)):xs) n p t
  | n == n', not (tableLabel tinfo `canFlowTo` l)
  = (Just t ==. lookupTable n (Pair n' (Table tinfo rs):xs) *** QED)
  ? assert ((Table tinfo rs) == t)
  ? labelSelectTableImplies l p t


simulationsSelect l ((Pair n' (Table tinfo rs)):xs) n p t
  | n == n', tableLabel tinfo `canFlowTo` l
  =   εTerm l (selectDB (εDB l ((Pair n' (Table tinfo rs)):xs)) n p) 
  ==. εTerm l (selectDB (Pair n' (εTable l (Table tinfo rs)):(εDB l xs)) n p) 
  ==. εTerm l (selectDB (Pair n' (Table tinfo (εRows l tinfo rs)):(εDB l xs)) n p) 
  ==. εTerm l (selectDB (Pair n' (Table tinfo (εRows l tinfo rs)):(εDB l xs)) n p)
  ==. εTerm l (selectRows p tinfo (εRows l tinfo rs))
      ?   (t   
       ==. fromJust (Just t)
       ==. fromJust (lookupTable n (Pair n' (Table tinfo rs):xs))
       ==. (Table tinfo rs) *** QED)
      ? assert ((Table tinfo rs) == t)       
      ? simulationsSelectRows l p tinfo rs 
  ==. εTerm l (selectRows p tinfo rs)
  ==. εTerm l (selectDB (Pair n' (Table tinfo rs):xs) n p)
  *** QED 

simulationsSelect l ((Pair n' (Table tinfo rs)):xs) n p _
  | n == n'
  = () 

simulationsSelect l (Pair n' (Table tinfo rs):ts) n p t
  =   εTerm l (selectDB (εDB l (Pair n' (Table tinfo rs):ts)) n p) 
  ==. εTerm l (selectDB (Pair n' (εTable l (Table tinfo rs)): εDB l ts) n p) 
  ==. εTerm l (selectDB (εDB l ts) n p)
       ? assert (lookupTable n (Pair n' (Table tinfo rs):ts) == lookupTable n ts)
       ? simulationsSelect l ts n p t 
  ==. εTerm l (selectDB ts n p)
  ==. εTerm l (selectDB (Pair n' (Table tinfo rs):ts) n p)
  *** QED 

{-@ simulationsSelectRows 
  :: (Label l, Eq l) 
  => l:l -> p:Pred 
  -> ti:TInfo l
  -> rs:{[Row l] | canFlowTo (labelSelectTable p (Table ti rs)) l} 
  -> { εTerm l (selectRows p ti (εRows l ti rs)) == εTerm l (selectRows p ti rs) } @-}
simulationsSelectRows :: (Label l, Eq l) => l -> Pred -> TInfo l -> [Row l] -> Proof 
simulationsSelectRows l p ti [] 
  =   εTerm l (selectRows p ti (εRows l ti [])) 
  ==. εTerm l (selectRows p ti [])
  *** QED 

simulationsSelectRows l p ti (r:rs) 
  | evalPred p r && evalPred p (εRow l ti r)
  =   εTerm l (selectRows p ti (εRows l ti (r:rs))) 
  ==. εTerm l (selectRows p ti (εRow l ti r:εRows l ti rs)) 
  ==. εTerm l (TCons (rowToTerm ti (εRow l ti r)) (selectRows p ti (εRows l ti rs))) 
  ==. TCons (εTerm l (rowToTerm ti (εRow l ti r))) (εTerm l (selectRows p ti (εRows l ti rs)))
      ? recursiveCall l ti p r rs 
      ? simulationsSelectRows l p ti rs 
 
      ? labelSelectTableImplies l p (Table ti rs)  
      ? simulationsRowTerm l p ti r 
  ==. TCons (εTerm l (rowToTerm ti r)) (εTerm l (selectRows p ti rs))
  ==. εTerm l (TCons (rowToTerm ti r) (selectRows p ti rs))
  ==. εTerm l (selectRows p ti (r:rs))
  *** QED 

simulationsSelectRows l p ti (r:rs) 
  | not (evalPred p r) && not (evalPred p (εRow l ti r))
  =   εTerm l (selectRows p ti (εRows l ti (r:rs))) 
  ==. εTerm l (selectRows p ti (εRow l ti r:εRows l ti rs)) 
  ==. εTerm l (selectRows p ti (εRows l ti rs)) 
      ? recursiveCall l ti p r rs 
      ? simulationsSelectRows l p ti rs  
  ==. εTerm l (selectRows p ti rs)
  ==. εTerm l (selectRows p ti (r:rs))
  *** QED 

simulationsSelectRows l p ti (r:rs) 
  = (labelSelectTable p (Table ti (r:rs)) ==.
     labelSelectRows p ti (r:rs) ==.  
     ((tableLabel ti `join` labelPredRow p ti r) `join` labelSelectRows p ti rs)
     *** QED 
     ) 
     ? joinCanFlowTo (tableLabel ti `join` labelPredRow p ti r) (labelSelectRows p ti rs) l 
     ? joinCanFlowTo (tableLabel ti) (labelPredRow p ti r) l 
     ? simulationsEvalPred p r l ti

   

{-@ simulationsRowTerm 
  :: Label l 
  => l:l -> p:Pred 
  -> ti:TInfo l  
  -> r:{Row l | canFlowTo (field1Label ti) l}
  -> { εTerm l (rowToTerm ti r) == εTerm l (rowToTerm ti (εRow l ti r)) } @-}
simulationsRowTerm :: (Eq l, Label l) => l -> Pred -> TInfo l -> Row l -> Proof 
simulationsRowTerm l p ti r@(Row k v1 v2) 
  | not (field1Label ti `canFlowTo` l)
  = assert False 

  | otherwise 
  =   εTerm l (rowToTerm ti (εRow l ti r))
  ==. εTerm l (rowToTerm ti (Row k v1' v2'))
  ==. εTerm l (TCons (TLabeled l1 v1') (TCons (TLabeled l2' v2') TNil))
  ==. TCons (εTerm l (TLabeled l1 v1')) (εTerm l (
      TCons (TLabeled l2' v2') TNil))
  ==. TCons (εTerm l (TLabeled l1 v1')) (
      TCons (εTerm l (TLabeled l2' v2')) (εTerm l TNil))
  ==. TCons (εTerm l (TLabeled l1 v1')) (
      TCons (εTerm l (TLabeled l2' v2')) (εTerm l TNil))
  ==. TCons (εTerm l (TLabeled l1 v1)) (
      TCons (εTerm l (TLabeled l2 v2)) (εTerm l TNil))
  ==. TCons (εTerm l (TLabeled l1 v1)) (εTerm l (
      TCons (TLabeled l2 v2) TNil))
  ==. εTerm l (TCons (TLabeled l1 v1 ) (TCons (TLabeled l2 v2)   TNil))
  ==. εTerm l (rowToTerm ti r)
  *** QED 
  where
    v1' = εTerm l v1
    v2' = if makeValLabel ti v1 `canFlowTo` l then εTerm l v2 else THole 
    l1  = field1Label ti
    l2  = makeValLabel ti v1
    l2' = makeValLabel ti v1'





recursiveCall :: (Eq l, Label l) => l -> TInfo l -> Pred -> Row l -> [Row l] -> Proof  
{-@ recursiveCall :: (Eq l, Label l) => l:l -> ti:TInfo l -> p:Pred -> r:Row l -> rs:[Row l] -> 
  {canFlowTo (labelSelectTable p (Table ti (r:rs))) l  => canFlowTo (labelSelectTable p (Table ti rs)) l } @-}   
recursiveCall l ti p r rs
  =  recursiveCallTrans ti p r rs &&& 
     lawFlowTransitivity (labelSelectTable p (Table ti rs)) (labelSelectTable p (Table ti (r:rs))) l


recursiveCallTrans :: (Eq l, Label l) => TInfo l -> Pred -> Row l -> [Row l] -> Proof  
{-@ recursiveCallTrans :: (Eq l, Label l) => ti:TInfo l -> p:Pred -> r:Row l -> rs:[Row l] -> 
  {canFlowTo (labelSelectTable p (Table ti rs)) (labelSelectTable p (Table ti (r:rs)))} @-}   
recursiveCallTrans ti p r rs 
  =   labelSelectTable p (Table ti (r:rs))
  ==. labelSelectRows p ti (r:rs) 
  ==. (tableLabel ti `join` labelPredRow p ti r) `join` labelSelectRows p ti rs
  ==. (tableLabel ti `join` labelPredRow p ti r) `join` labelSelectTable p (Table ti rs)
      ? unjoinCanFlowToItself (tableLabel ti `join` labelPredRow p ti r) (labelSelectTable p (Table ti rs))
  *** QED 


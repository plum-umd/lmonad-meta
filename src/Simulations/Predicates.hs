{-@ LIQUID "--reflection"  @-}

module Simulations.Predicates where

import ProofCombinators
import Labels 
import Programs 
import Predicates 

import Idempotence 
import Simulations.Terms 

import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsEvalPred
 :: p : Pred
 -> r : Row l
 -> l : l
 -> ti : {TInfo l | canFlowTo (labelPredRow p ti r) l }
 -> { evalPred p r == evalPred p (εRow l ti r) }
 @-}
simulationsEvalPred :: (Eq l, Label l) => Pred -> Row l -> l -> TInfo l -> Proof
simulationsEvalPred p r@(Row k v1 v2) l ti 
  | pDep1 p && pDep2 p
  =   evalPred p (εRow l ti r)
      ? assert (canFlowTo (labelPredRow p ti r) l)
      ? assert (labelPredRow p ti r == (field1Label ti `join` makeValLabel ti (rowField1 r)))
      ? joinCanFlowTo (field1Label ti) (makeValLabel ti (rowField1 r)) l 
  ==. evalPred p (Row k (εTerm l v1) (εTerm l v2))
  ==. evalPred p r
  *** QED 
  | pDep1 p
  =   evalPred p (εRow l ti r)
      ? assert (canFlowTo (labelPredRow p ti r) l)
      ? assert (labelPredRow p ti r == field1Label ti)
  ==. evalPred p (Row k (εTerm l v1) v2')
  ==. evalPredicate p (εTerm l v1)
  ==. evalPredicate p v1
  ==. evalPred p r
  *** QED 
  | otherwise 
  =   evalPred p (εRow l ti r)
  ==. pVal p 
  ==. evalPred p r
  *** QED 
  where
    v2' = if makeValLabel ti v1 `canFlowTo` l then εTerm l v2 else THole 



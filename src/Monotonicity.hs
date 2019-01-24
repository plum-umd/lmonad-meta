{-@ LIQUID "--reflection"  @-}

module Monotonicity where

import ProofCombinators 
import Labels 
import Programs 
import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ monotonicEval :: Label l => p:{Program l | isPg p && terminates p }
     -> { canFlowTo (pLabel p) (pLabel (eval p)) } 
     / [evalSteps p, 0] @-}
monotonicEval :: (Eq l, Label l) => Program l -> Proof

monotonicEval pg@(Pg lc db (TUpdate n tp  (TJust (TLabeled l1 v1)) _))
  | Just t <- lookupTable n db
  , TPred p <- tp
  = let lc' = lc `join` ((field1Label (tableInfo t) `join` l1) `join` tableLabel (tableInfo t)) in 
    if (pLabel (eval pg) == lc') 
     then lawJoin lc' lc ((field1Label (tableInfo t) `join` l1) `join` tableLabel (tableInfo t)) lc'
     else lawFlowReflexivity lc
monotonicEval pg@(Pg lc db (TUpdate n _ _ _))
  =   assert (pLabel (eval pg) == lc) 
  &&& lawFlowReflexivity lc


monotonicEval pg@(Pg lc db (TSelect n tp)) 
  | Just t <- lookupTable n db 
  , TPred p <- tp 
  = let lc' = lc `join` labelSelectTable p t in 
    if (pLabel (eval pg) == lc') 
      then lawJoin lc' lc (labelSelectTable p t) lc'
      else lawFlowReflexivity lc
monotonicEval pg@(Pg lc db (TSelect _ _))
  =   assert (pLabel (eval pg) == lc) 
  &&& lawFlowReflexivity lc

monotonicEval pg@(Pg lc db (TDelete n tp)) 
  | Just t  <- lookupTable n db 
  , TPred p <- tp 
  = let lc' = lc `join` labelReadTable p (tableInfo t) in 
    if (pLabel (eval pg) == lc') 
      then lawJoin lc' lc (labelReadTable p (tableInfo t)) lc'
      else lawFlowReflexivity lc
monotonicEval pg@(Pg lc db (TDelete _ _))
  =   assert (pLabel (eval pg) == lc) 
  &&& lawFlowReflexivity lc


monotonicEval pg@(Pg lc db (TInsert n t1 t2))
  | TLabeled l1 _ <- t1 
  = let lc' = l1 `join` lc in 
    if (pLabel (eval pg) == lc') 
      then lawJoin lc' l1 lc lc'
      else lawFlowReflexivity lc
monotonicEval pg@(Pg lc db (TInsert _ _ _))
  =   assert (pLabel (eval pg) == lc) 
  &&& lawFlowReflexivity lc


monotonicEval (Pg lc db (TUnlabel (TLabeled l t))) 
  =   eval (Pg lc db (TUnlabel (TLabeled l t)))
  ==. Pg (lc `join` l) db (TReturn t)
      ? lawJoin (lc `join` l) lc l lc
      ? lawFlowTransitivity lc lc (lc `join` l)
      ? assert (canFlowTo lc (lc `join` l))
  *** QED 

monotonicEval (Pg lc db (TUnlabel t)) 
  =   pLabel (eval (Pg lc db (TUnlabel t)))
  ==. pLabel (Pg lc db (evalTerm t))
      ? lawFlowReflexivity lc &&& assert (canFlowTo lc lc)
  *** QED 

monotonicEval p@(Pg lc db (TBind t1 t2))
  | Pg lc' db' (TLIO t1') <- evalStar (Pg lc db t1)
  =   (eval p ==. Pg lc' db' (TApp t2 t1') *** QED)
  &&& (evalStar (Pg lc db t1) ==. Pg lc' db' (TLIO t1') *** QED)
  &&& evalStepsBindAxiom lc db t1 t2  
  &&& monotonicEvalStar (Pg lc db t1)
  &&& assert (canFlowTo (pLabel (Pg lc db t1)) (pLabel (evalStar (Pg lc db t1))))
  &&& assert (canFlowTo lc lc')
  &&& assert (canFlowTo (pLabel p) (pLabel (eval p)))

monotonicEval (Pg lc db (TBind t1 t2))
  =   pLabel (eval (Pg lc db (TBind t1 t2)))
  ==. pLabel (Pg lc db TException)
      ? lawFlowReflexivity lc 
  *** QED 


monotonicEval (Pg lc db (TToLabeled (TVLabel ll) t)) 
  | not (lc `canFlowTo` ll)
  =   eval (Pg lc db (TToLabeled (TVLabel ll) t)) 
  ==. Pg lc db (TLIO TException)
      ? lawFlowReflexivity lc
  *** QED 

monotonicEval (Pg lc db (TToLabeled (TVLabel ll) t)) 
  | Pg lc' db' (TLIO t') <- evalStar (Pg lc db t)
  , lc' `canFlowTo` ll
  =   eval (Pg lc db (TToLabeled (TVLabel ll) t)) 
  ==. Pg lc db' (TLIO (TLabeled ll t'))
      ? lawFlowReflexivity lc
  *** QED 

monotonicEval (Pg lc db (TToLabeled (TVLabel ll) t)) 
  | Pg _ db' _ <- evalStar (Pg lc db t)
  =   eval (Pg lc db (TToLabeled (TVLabel ll) t)) 
  ==. Pg lc db' (TLIO (TLabeled ll TException))
      ? lawFlowReflexivity lc
  *** QED 

monotonicEval (Pg lc db (TToLabeled t1 t2))
  =   eval (Pg lc db (TToLabeled t1 t2))
  ==. Pg lc db (TToLabeled (evalTerm t1) t2)
      ? lawFlowReflexivity lc
  *** QED 

monotonicEval (Pg lc db t) 
  =   pLabel (Pg lc db t)
  ==. pLabel (eval ((Pg lc db t)))
      ? lawFlowReflexivity lc &&& assert (canFlowTo lc lc)
  *** QED 

{-@ monotonicEvalStar :: Label l => p:{Program l | isPg p && terminates p }
     -> { canFlowTo (pLabel p) (pLabel (evalStar p)) } 
    / [evalSteps p, 1] @-}
monotonicEvalStar :: (Eq l, Label l) => Program l -> Proof
monotonicEvalStar (Pg lc db t) | isValue t
  =   pLabel (Pg lc db t)
  ==. pLabel (evalStar (Pg lc db t))
      ? lawFlowReflexivity lc &&& assert (canFlowTo lc lc)
  *** QED 
monotonicEvalStar p@(Pg lc db t)
  =   (evalStar p ==. evalStar (eval p) *** QED)
  &&& evalStepsNatAxiom p 
  &&& monotonicEval p 
  &&& assert (pLabel p `canFlowTo` pLabel (eval p))
  &&& evalStepsAxiom p 
  &&& monotonicEvalStar (eval p) 
  &&& assert (pLabel (eval p) `canFlowTo` pLabel (evalStar (eval p)))
  &&& lawFlowTransitivity (pLabel p) (pLabel (eval p)) (pLabel (evalStar (eval p)))

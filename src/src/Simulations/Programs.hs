{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}
{-@ LIQUID "--trustinternals"                           @-}

{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}

module Simulations.Programs where

import Label
import Language
import Programs 
import MetaFunctions
import Termination
import Simulations.Helpers

import ProofCombinators


{-@ monotonicLabelEvalProgram
 :: p:{Program | ς p && terminates p }
 -> { canFlowTo (pLabel p) (pLabel (evalProgram p)) }
 / [evalSteps p, 0] 
 @-}
monotonicLabelEvalProgram :: Program -> Proof
monotonicLabelEvalProgram PgHole 
  = unreachable 

monotonicLabelEvalProgram p@(Pg l c m (TBind t1 t2)) 
  = case evalProgramStar (Pg l c m t1) of 
      PgHole              -> ()
      p'@(Pg l' c' m' t') -> (evalProgram p == Pg l' c' m' (TApp t2 t') *** QED)
                             &&& safeProgramBindsToSafeProgram p t1 t2 
                             &&& terminationAxiomTBind l c m t1 t2 
                             &&& monotonicLabelEvalProgramStar (Pg l c m t1)

monotonicLabelEvalProgram p@(Pg lc cc m (TUnlabel (TLabeledTCB ll t)))
  = let l' = lc `join` ll in
    if l' `canFlowTo` cc 
      then (canFlowTo lc l' *** QED) &&& canFlowToJoin lc ll l'  
      else (canFlowTo lc lc *** QED) &&& reflexiveLabel lc 

  where
    p' = evalProgram p  

monotonicLabelEvalProgram p@(Pg l _ _ _) 
  = canFlowTo (pLabel p) (pLabel (evalProgram p)) ==. True ? reflexiveLabel l 
  *** QED  

   
{-@ monotonicLabelEvalProgramStar
 :: p:{Program | ς p && terminates p }
 -> { canFlowTo (pLabel p) (pLabel (evalProgramStar p)) }
 / [evalSteps p, 1] 
 @-}
monotonicLabelEvalProgramStar :: Program  -> Proof

monotonicLabelEvalProgramStar p@(Pg l c m t) | isValue t 
  =   canFlowTo (pLabel p) (pLabel (evalProgramStar p))
  ==. canFlowTo l l ? reflexiveLabel l  
  *** QED 
monotonicLabelEvalProgramStar p 
  =   (canFlowTo l l'' *** QED)
  &&& (evalProgramStar p == p'' *** QED)
  &&& terminationAxiom p
  &&& safeTheorem p
  &&& monotonicLabelEvalProgram p 
  &&& monotonicLabelEvalProgramStar p'
  &&& transitiveLabel l l' l'' 
   
  where
    l   = pLabel p
    l'  = pLabel p'
    l'' = pLabel (evalProgramStar p'')
    p'  = evalProgram p 
    p'' = evalProgramStar p'




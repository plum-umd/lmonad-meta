{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}
{-@ LIQUID "--trustinternals"                           @-}

{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
module Simulations.Programs where

import Label
import Language
import Programs 
import MetaFunctions 

import ProofCombinators


{-@ automatic-instances monotonicLabelEvalProgram @-}
{-@ monotonicLabelEvalProgram
 :: n' : Index
 -> p : Program
 -> {p' : Program | evalProgram p == (Pair n' p')}
 -> {v : Proof | canFlowTo (pLabel p) (pLabel p')}
 @-}
monotonicLabelEvalProgram :: Index -> Program -> Program -> Proof
monotonicLabelEvalProgram n' p p' = ()



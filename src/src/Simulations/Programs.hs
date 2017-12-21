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


-- {-@ automatic-instances monotonicLabelEvalProgram @-}
{-@ monotonicLabelEvalProgram
 :: p : Program
 -> n' : Index
 -> {p' : Program | evalProgram p == (Pair n' p')}
 -> {v : Proof | canFlowTo (pLabel p) (pLabel p')}
 @-}
monotonicLabelEvalProgram :: Program -> Index -> Program -> Proof
-- monotonicLabelEvalProgram PgHole n' p' = unreachable
monotonicLabelEvalProgram p@(Pg l c m TGetLabel) 0 (Pg l' c' m' (TVLabel l'')) = 
        canFlowTo l l'
    ==: canFlowTo l l ? (l == l' *** QED)
    ==! True
    *** QED
monotonicLabelEvalProgram p n' p' = undefined

{-@ monotonicLabelEvalProgramStar
 :: n : Index
 -> p : Program
 -> n' : Index
 -> {p' : Program | evalProgramStar (Pair n p) == (Pair n' p')}
 -> {v : Proof | canFlowTo (pLabel p) (pLabel p')}
 @-}
monotonicLabelEvalProgramStar :: Index -> Program -> Index -> Program -> Proof
monotonicLabelEvalProgramStar n p n' p' =
    undefined
    -- TODO: Unimplemented XXX


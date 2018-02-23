{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}

module Simulations.EraseEvalErase where

import Label
import Language
import Programs
import MetaFunctions

import ProofCombinators


{-@ eraseEvalEraseSimulation
 :: l : Label 
 -> t : Term 
 -> {εTerm l (eval (εTerm l t)) == εTerm l (eval t)}
 / [size t]
 @-}
eraseEvalEraseSimulation :: Label -> Term -> Proof
eraseEvalEraseSimulation = undefined

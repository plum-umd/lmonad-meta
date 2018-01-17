{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}

module Simulations.MetaFunctions where

import Label
import Language
import Programs
import MetaFunctions

import ProofCombinators

{-@ εTermIdempotent 
 :: l : Label 
 -> t : Term 
 -> {v : Proof | εTerm l (εTerm l t) == εTerm l t}
 @-}
εTermIdempotent :: Label -> Term -> Proof
εTermIdempotent _ _ = undefined

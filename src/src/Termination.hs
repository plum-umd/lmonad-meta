-- Axiomatization of Program Termination 

{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}
{-@ LIQUID "--trustinternals"                           @-}

{-# LANGUAGE CPP                                        #-}

module Termination where

import Language
import Programs
import Label

import ProofCombinators

{-@ measure terminates :: Program -> Bool @-}
{-@ measure evalSteps  :: Program -> Int  @-}
{-@ invariant {p:Program | 0 <= evalSteps p } @-}

{-@ assume terminationAxiom :: {p:Program | terminates p } 
  -> {  evalSteps (evalProgram p) < evalSteps p && terminates (evalProgram p) } @-}
terminationAxiom :: Program -> Proof 
terminationAxiom _ = ()


{-@ assume terminationAxiomTBind 
  :: l:Label -> c:Label -> m:Memory -> t1:Term -> t2:Term
  -> { (evalSteps (Pg l c m t1) < evalSteps (Pg l c m (TBind t1 t2))) &&
       (terminates (Pg l c m (TBind t1 t2)) => terminates (Pg l c m t1)) 
     } 
  @-}
terminationAxiomTBind :: Label -> Label -> Memory -> Term -> Term -> Proof 
terminationAxiomTBind _ _ _ _ _ = ()



-- Axiomatization of Program Termination 

{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}
{-@ LIQUID "--trustinternals"                           @-}

{-# LANGUAGE CPP                                        #-}

module Termination where

import Language
import Programs
import Label
import MetaFunctions

import ProofCombinators

{-@ measure terminates :: Program -> Bool @-}
{-@ measure evalSteps  :: Program -> Int  @-}
{-@ invariant {p:Program | 0 <= evalSteps p } @-}

{-@ assume terminationAxiom :: {p:Program | terminates p } 
  -> {  evalSteps (evalProgram p) < evalSteps p && terminates (evalProgram p) } @-}
terminationAxiom :: Program -> Proof 
terminationAxiom _ = ()

-- {-@ terminatesBind
--  :: lc : Label
--  -> c : Label
--  -> m : Database
--  -> t1 : Term
--  -> t2 : {Term | terminates (Pg lc c m (TBind t1 t2))}
--  -> {terminates (Pg lc c m t1)}
--  @-}
-- terminatesBind :: Label -> Label -> Database -> Term -> Term -> Proof
-- terminatesBind _ _ _ _ _ = ()

{-@ assume terminationAxiomErase 
  :: l:Label -> {p:Program | terminates p }
  -> {  evalSteps (evalProgram (ε l p)) < evalSteps p && terminates (evalProgram (ε l p)) } @-}
terminationAxiomErase :: Label -> Program -> Proof 
terminationAxiomErase _ _ = ()

-- {-@ assume terminationAxiomTBind 
--   :: l:Label -> c:Label -> m:Database -> t1:Term -> t2:Term
--   -> { (evalSteps (Pg l c m t1) < evalSteps (Pg l c m (TBind t1 t2))) &&
--        (terminates (Pg l c m (TBind t1 t2)) => terminates (Pg l c m t1)) 
--      } 
--   @-}
--
--   :: l:Label -> c:Label -> m:Database -> t1:Term -> t2:Term
--   -> { (evalSteps (Pg l c m t1) < evalSteps (Pg l c m (TBind t1 t2))) &&
--        (terminates (Pg l c m (TBind t1 t2)) => terminates (Pg l c m t1)) 
--      } 
{-@ assume terminationAxiomTBind 
  :: l:Label -> c:Label -> m:Database -> t1:Term -> {t2:Term | terminates (Pg l c m (TBind t1 t2))}
  -> { terminates (Pg l c m t1) && evalSteps (Pg l c m t1) < evalSteps (Pg l c m (TBind t1 t2)) }
  @-}
terminationAxiomTBind :: Label -> Label -> Database -> Term -> Term -> Proof 
terminationAxiomTBind _ _ _ _ _ = ()


{-@ assume terminationAxiomTToLabeled 
  :: l:Label -> c:Label -> m:Database -> t1:Term -> t2:Term
  -> { (evalSteps (Pg l c m t2) < evalSteps (Pg l c m (TToLabeled t1 t2))) &&
       (terminates (Pg l c m (TToLabeled t1 t2)) => terminates (Pg l c m t2)) 
     } 
  @-}
terminationAxiomTToLabeled :: Label -> Label -> Database -> Term -> Term -> Proof 
terminationAxiomTToLabeled _ _ _ _ _ = ()


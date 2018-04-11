{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}
{-@ LIQUID "--max-case-expand=0"                        @-}

module Simulations where

import Label
import Language
import Programs 
import MetaFunctions 
import Simulations.Language
import Simulations.MetaFunctions
import Simulations.Programs
import Simulations.Helpers
import Simulations.EraseEvalErase
import Termination

import  ProofCombinators

{-@ simulationsCorollary 
  :: p:{Program | ς p && terminates p} 
  -> p':Program 
  -> l:Label
  -> {v:Proof | evalProgram p == p'}
  -> {evalEraseProgram (ε l p) l = ε l p'} @-}
simulationsCorollary :: Program -> Program -> Label -> Proof -> Proof
simulationsCorollary p p' l evalProp = simulations p p' l evalProp

simulations :: Program -> Program -> Label -> Proof -> Proof
{-@ simulations 
  :: {p:Program | ς p && terminates p} -> p':Program -> l:Label
  -> {v:Proof | evalProgram p == p'}
  -> {v:Proof | evalEraseProgram (ε l p) l = ε l p'} @-}
simulations p p' l evalProp 
  =   evalEraseProgram (ε l p) l
  ==. ε l (evalProgram p) ? simulations' p l
  ==. ε l p' ? evalProp
  *** QED

simulations' :: Program -> Label -> Proof
{-@ simulations' 
  :: {p:Program | ς p && terminates p} 
  -> l:Label
  -> {v:Proof | evalEraseProgram (ε l p) l = ε l (evalProgram p)} @-}

simulations' (Pg lcurr c m t) l | not (lcurr `canFlowTo` l) -- l < lcurr
    = simulationsHoles' (Pg lcurr c m t) l

simulations' p l {- | lcurr <= l -}
  = simulations'' p l

{-@ simulationsStar
 :: {p : Program | terminates p}
 -> l : Label
 -> {v : Proof | ε l (evalProgramStar (ε l p)) = ε l (evalProgramStar p)}
 / [evalSteps p, 3]
 @-}
simulationsStar :: Program -> Label -> Proof
simulationsStar p l | canFlowTo (pLabel p) l = simulationsStar'' p l
simulationsStar p l = simulationsStar' p l

{-@ simulationsStar' 
 :: {p : Program | terminates p}
 -> {l : Label | not (canFlowTo (pLabel p) l)}
 -> {v : Proof | ε l (evalProgramStar (ε l p)) = ε l (evalProgramStar p)}
 / [evalSteps p, 2]
 @-}
simulationsStar' :: Program -> Label -> Proof
simulationsStar' PgHole l = 
        ε l (evalProgramStar (ε l PgHole))  
    ==. ε l (evalProgramStar PgHole)
    *** QED

simulationsStar' p@(Pg lc c m t) l = -- | isValue t = 
        ε l (evalProgramStar (ε l p))  
    ==! ε l (evalProgramStar PgHole)
    ==! ε l PgHole
    ==! PgHole
    ==: ε l p' ?
            monotonicLabelEvalProgramStar p
        &&& greaterLabelNotFlowTo lc lc' l
    ==! ε l (evalProgramStar (Pg lc c m t))
    *** QED 

    where
        p'@(Pg lc' _ _ _) = evalProgramStar p


{-@ simulationsStar'' 
 :: {p : Program | terminates p}
 -> {l : Label | canFlowTo (pLabel p) l}
 -> {v : Proof | ε l (evalProgramStar (ε l p)) = ε l (evalProgramStar p)}
 / [evalSteps p, 2]
 @-}
simulationsStar'' :: Program -> Label -> Proof
simulationsStar'' (Pg lp c m t) l | isValue t
  =   ε l (evalProgramStar (ε l (Pg lp c m t)))  
  ==. ε l (evalProgramStar (Pg lp c m (εTerm l t)))  
  ==. ε l (Pg lp c m (εTerm l t))  
  ==. Pg lp c m (εTerm l (εTerm l t))  
      ? εTermIdempotent l t 
  ==. Pg lp c m (εTerm l t)
      ? valueEterm l t 
  ==. ε l (Pg lp c m t)
  ==. ε l (evalProgramStar (Pg lp c m t))
  *** QED 

simulationsStar'' p@(Pg _ _ _ t) l | not (isValue t)
  =   ε l (evalProgramStar (ε l p)) 
  ==. ε l (evalProgramStar (evalProgram (ε l p)))
      ? valueEterm l t
  ==. ε l (evalProgramStar (ε l (evalProgram (ε l p))))
      ?   terminationAxiomErase l p
      &&& simulationsStar (evalProgram (ε l p)) l 
  ==. ε l (evalProgramStar (evalEraseProgram (ε l p) l))
      ? simulations'' p l 
  ==. ε l (evalProgramStar (ε l (evalProgram p)))
      ?  terminationAxiom p
      &&& simulationsStar (evalProgram p) l 
  ==. ε l (evalProgramStar (evalProgram p))
  ==. ε l (evalProgramStar p)
  *** QED 

simulationsStar'' p@PgHole l
  =   ε l (evalProgramStar (ε l p)) 
  ==. ε l (evalProgramStar p)
  *** QED 


{-@ simulations'' 
 :: {p : Program | terminates p} 
 -> {l : Label | canFlowTo (pLabel p) l}
 -> {v : Proof | evalEraseProgram (ε l p) l = ε l (evalProgram p)}
 / [evalSteps p, 1]
 @-}
simulations'' :: Program -> Label -> Proof
simulations'' p@PgHole l =
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram p)
        *** QED

simulations'' p@(Pg lc c m t@THole) l =
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (evalProgram (Pg lc c m t))
        ==. ε l (evalProgram p)
        *** QED

simulations'' p@(Pg lc c m t@(TLam v t1)) l = case propagateException t of
    True -> 
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l (TLam v t1))))
        ==. ε l (Pg lc c m (eval (εTerm l (TLam v t1))))
        ==. Pg lc c m (εTerm l (eval (εTerm l (TLam v t1))))
        ==. Pg lc c m (εTerm l (eval (TLam v t1))) ? propagateErasePropagates l t
        ==. Pg lc c m (εTerm l TException)
        ==. Pg lc c m TException
        ==. Pg lc c m (εTerm l TException)
        ==. ε l (Pg lc c m TException)
        ==. ε l (Pg lc c m (eval (TLam v t1))) -- ? propagateExceptionFalseEvalsToNonexception t
        ==. ε l (evalProgram p)
        *** QED
    False ->
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l (TLam v t1))))
        ==. ε l (evalProgram (Pg lc c m (TLam v (εTerm l t1))))
        ==. ε l (Pg lc c m (eval (TLam v (εTerm l t1))))
        ==. ε l (Pg lc c m (TLam v (εTerm l t1))) ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalseEvalsToNonexception l t
        ==. Pg lc c m (εTerm l (TLam v (εTerm l t1)))
        ==. Pg lc c m (TLam v (εTerm l (εTerm l t1)))
        ==. Pg lc c m (TLam v (εTerm l t1)) ? εTermIdempotent l t1
        ==. Pg lc c m (εTerm l (TLam v t1))
        ==. ε l (Pg lc c m (TLam v t1))
        ==. ε l (Pg lc c m (eval (TLam v t1))) ? propagateExceptionFalseEvalsToNonexception t
        ==. ε l (evalProgram p)
        *** QED

simulations'' p@(Pg lc c m t@(TIf t1 t2 t3)) l = case propagateException t of
    True ->
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (Pg lc c m (eval (εTerm l t)))
        ==. ε l (Pg lc c m TException) ? propagateErasePropagates l t
        ==. ε l (Pg lc c m (eval t))
        ==. ε l (evalProgram p)
        *** QED
    False -> 
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (Pg lc c m (eval (εTerm l t)))
        ==. Pg lc c m (εTerm l (eval (εTerm l t)))
        ==. Pg lc c m (εTerm l (eval t)) ? eraseEvalEraseSimulation l t
        ==. ε l (Pg lc c m (eval t))
        ==. ε l (evalProgram p)
        *** QED

simulations'' p@(Pg lc c m t@(TFix _)) l = case propagateException t of
    True ->
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (Pg lc c m (eval (εTerm l t)))
        ==. ε l (Pg lc c m TException) ? propagateErasePropagates l t
        ==. ε l (Pg lc c m (eval t))
        ==. ε l (evalProgram p)
        *** QED
    False -> 
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (Pg lc c m (eval (εTerm l t)))
        ==. Pg lc c m (εTerm l (eval (εTerm l t)))
        ==. Pg lc c m (εTerm l (eval t)) ? eraseEvalEraseSimulation l t
        ==. ε l (Pg lc c m (eval t))
        ==. ε l (evalProgram p)
        *** QED

simulations'' p@(Pg lc c m t@(TJoin _ _)) l = case propagateException t of
    True ->
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (Pg lc c m (eval (εTerm l t)))
        ==. ε l (Pg lc c m TException) ? propagateErasePropagates l t
        ==. ε l (Pg lc c m (eval t))
        ==. ε l (evalProgram p)
        *** QED
    False -> 
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (Pg lc c m (eval (εTerm l t)))
        ==. Pg lc c m (εTerm l (eval (εTerm l t)))
        ==. Pg lc c m (εTerm l (eval t)) ? eraseEvalEraseSimulation l t
        ==. ε l (Pg lc c m (eval t))
        ==. ε l (evalProgram p)
        *** QED

simulations'' p@(Pg lc c m t@(TMeet _ _)) l = case propagateException t of
    True ->
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (Pg lc c m (eval (εTerm l t)))
        ==. ε l (Pg lc c m TException) ? propagateErasePropagates l t
        ==. ε l (Pg lc c m (eval t))
        ==. ε l (evalProgram p)
        *** QED
    False -> 
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (Pg lc c m (eval (εTerm l t)))
        ==. Pg lc c m (εTerm l (eval (εTerm l t)))
        ==. Pg lc c m (εTerm l (eval t)) ? eraseEvalEraseSimulation l t
        ==. ε l (Pg lc c m (eval t))
        ==. ε l (evalProgram p)
        *** QED

simulations'' p@(Pg lc c m t@(TApp t1 t2)) l = case (propagateException t1, propagateException t2) of
    (True, _) ->
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l (TApp t1 t2))))
        ==. ε l (evalProgram (Pg lc c m (TApp (εTerm l t1) (εTerm l t2))))
        ==. ε l (Pg lc c m (eval (TApp (εTerm l t1) (εTerm l t2))))
        ==. ε l (Pg lc c m TException) ? propagateErasePropagates l t1
        ==. ε l (Pg lc c m (eval t))
        ==. ε l (evalProgram p)
        *** QED
    (False, True) ->
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l (TApp t1 t2))))
        ==. ε l (evalProgram (Pg lc c m (TApp (εTerm l t1) (εTerm l t2))))
        ==. ε l (Pg lc c m (eval (TApp (εTerm l t1) (εTerm l t2))))
        ==. ε l (Pg lc c m TException) ? propagateErasePropagates l t2
        ==. ε l (Pg lc c m (eval t))
        ==. ε l (evalProgram p)
        *** QED
    (False, False) ->
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (Pg lc c m (eval (εTerm l t)))
        ==. Pg lc c m (εTerm l (eval (εTerm l t)))
        ==. Pg lc c m (εTerm l (eval t)) ? eraseEvalEraseSimulation l t
        ==. ε l (Pg lc c m (eval t))
        ==. ε l (evalProgram p)
        *** QED

simulations'' p@(Pg lc c m t@(TCanFlowTo _ _)) l = case propagateException t of
    True ->
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (Pg lc c m (eval (εTerm l t)))
        ==. ε l (Pg lc c m TException) ? propagateErasePropagates l t
        ==. ε l (Pg lc c m (eval t))
        ==. ε l (evalProgram p)
        *** QED
    False -> 
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (Pg lc c m (eval (εTerm l t)))
        ==. Pg lc c m (εTerm l (eval (εTerm l t)))
        ==. Pg lc c m (εTerm l (eval t)) ? eraseEvalEraseSimulation l t
        ==. ε l (Pg lc c m (eval t))
        ==. ε l (evalProgram p)
        *** QED

simulations'' p@(Pg lc c m t@(TBind t1 t2)) l =
        evalEraseProgram (ε l p) l 
    ==. evalEraseProgram (Pg lc c m (εTerm l t)) l
    ==. evalEraseProgram (Pg lc c m (TBind (εTerm l t1) (εTerm l t2))) l
    ==. ε l (evalProgram p) ? simulationsTBind l lc c m t1 t2 
    *** QED 

simulations'' p@(Pg lc c m t@(TLowerClearance (TVLabel c'))) l =
        evalEraseProgram (ε l p) l
    ==. ε l (evalProgram (ε l p))
    ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
    ==. ε l (evalProgram (Pg lc c m (TLowerClearance (εTerm l (TVLabel c')))))
    ==. ε l (evalProgram (Pg lc c m (TLowerClearance (TVLabel c'))))
    ==. ε l (evalProgram p)
    *** QED

simulations'' p@(Pg lc c m t@(TLowerClearance t1)) l = case propagateException t of
    True ->
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (evalProgram (Pg lc c m (TLowerClearance (εTerm l t1))))
        ==. ε l (Pg lc c m (eval (TLowerClearance (εTerm l t1)))) ? eraseNotTVLabel l t1 -- assert (not (isTVLabel (εTerm l t1)))
        ==. ε l (Pg lc c m TException) ? propagateErasePropagates l t
        ==. ε l (Pg lc c m (eval t))
        ==. ε l (evalProgram p)
        *** QED
    False -> 
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (evalProgram (Pg lc c m (TLowerClearance (εTerm l t1))))
        ==. ε l (Pg lc c m (eval (TLowerClearance (εTerm l t1)))) ? eraseNotTVLabel l t1
        ==. ε l (Pg lc c m (eval (εTerm l t)))
        ==. Pg lc c m (εTerm l (eval (εTerm l t)))
        ==. Pg lc c m (εTerm l (eval t)) ? eraseEvalEraseSimulation l t
        ==. ε l (Pg lc c m (eval t))
        ==. ε l (evalProgram p)
        *** QED

simulations'' p@(Pg lc c m t@(TUnlabel t1'@(TLabeledTCB ll t1))) l = case l' `canFlowTo` c of
    True ->
        if ll `canFlowTo` l then
                evalEraseProgram (ε l p) l
            ==. ε l (evalProgram (ε l p))
            ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
            ==. ε l (evalProgram (Pg lc c m (TUnlabel (εTerm l t1'))))
            ==. ε l (evalProgram (Pg lc c m (TUnlabel (TLabeledTCB ll (εTerm l t1)))))
            ==. ε l (Pg l' c m (εTerm l t1))
            ==. Pg l' c m (εTerm l (εTerm l t1))
            ==. Pg l' c m (εTerm l t1) ? εTermIdempotent l t1
            ==. ε l (Pg l' c m t1)
            ==. ε l (evalProgram p)
            *** QED
        else
                evalEraseProgram (ε l p) l
            ==. ε l (evalProgram (ε l p))
            ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
            ==. ε l (evalProgram (Pg lc c m (TUnlabel (εTerm l t1'))))
            ==. ε l (evalProgram (Pg lc c m (TUnlabel (TLabeledTCB ll THole))))
            ==. ε l (Pg l' c m THole) -- JP: Why is this THole not used?
            ==. PgHole ?
                assert (not (l' `canFlowTo` l))
            ==. ε l (Pg l' c m t1)
            ==. ε l (evalProgram p)
            *** QED

    False ->
        if ll `canFlowTo` l then
                evalEraseProgram (ε l p) l
            ==. ε l (evalProgram (ε l p))
            ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
            ==. ε l (evalProgram (Pg lc c m (TUnlabel (εTerm l t1'))))
            ==. ε l (evalProgram (Pg lc c m (TUnlabel (TLabeledTCB ll (εTerm l t1)))))
            ==. ε l (Pg lc c m TException)
            ==. ε l (evalProgram p)
            *** QED
        else
                evalEraseProgram (ε l p) l
            ==. ε l (evalProgram (ε l p))
            ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
            ==. ε l (evalProgram (Pg lc c m (TUnlabel (εTerm l t1'))))
            ==. ε l (evalProgram (Pg lc c m (TUnlabel (TLabeledTCB ll THole))))
            ==. ε l (evalProgram (Pg lc c m (TUnlabel (TLabeledTCB ll THole))))
            ==. ε l (Pg lc c m TException)
            ==. ε l (evalProgram p)
            *** QED

    where
        l' = lc `join` ll

simulations'' p@(Pg lc c m t@(TUnlabel t1)) l = case propagateException t of
    True ->
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (evalProgram (Pg lc c m (TUnlabel (εTerm l t1))))
        ==. ε l (Pg lc c m (eval (TUnlabel (εTerm l t1))))
        ==. ε l (Pg lc c m TException) ? propagateErasePropagates l t
        ==. ε l (Pg lc c m (eval (TUnlabel t1)))
        ==. ε l (evalProgram (Pg lc c m (TUnlabel (εTerm l t1))))
        ==. ε l (evalProgram p)
        *** QED
    False ->
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (evalProgram (Pg lc c m (TUnlabel (εTerm l t1))))
        ==. ε l (Pg lc c m (eval (TUnlabel (εTerm l t1))))
        ==. ε l (Pg lc c m (eval (εTerm l t)))
        ==. Pg lc c m (εTerm l (eval (εTerm l t)))
        ==. Pg lc c m (εTerm l (eval t)) ? eraseEvalEraseSimulation l t
        ==. ε l (evalProgram p)
        *** QED

simulations'' p@(Pg lc c m t@(TLabel t1@(TVLabel ll) t2)) l | lc `canFlowTo` ll && ll `canFlowTo` c =
    if ll `canFlowTo` l then
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (evalProgram (Pg lc c m (TLabel (εTerm l t1) (εTerm l t2))))
        ==. ε l (evalProgram (Pg lc c m (TLabel t1 (εTerm l t2))))
        ==. ε l (Pg lc c m (TLabeledTCB ll (εTerm l t2)))
        ==. Pg lc c m (εTerm l (TLabeledTCB ll (εTerm l t2)))
        ==. Pg lc c m (TLabeledTCB ll (εTerm l (εTerm l t2)))
        ==. Pg lc c m (TLabeledTCB ll (εTerm l t2))
            ? εTermIdempotent l t2
        ==. Pg lc c m (εTerm l (TLabeledTCB ll t2))
        ==. ε l (Pg lc c m (TLabeledTCB ll t2))
        ==. ε l (evalProgram p)
        *** QED
    else
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (evalProgram (Pg lc c m (TLabel (εTerm l t1) (εTerm l t2))))
        ==. ε l (evalProgram (Pg lc c m (TLabel t1 (εTerm l t2))))
        ==. ε l (Pg lc c m (TLabeledTCB ll (εTerm l t2)))
        ==. Pg lc c m (εTerm l (TLabeledTCB ll (εTerm l t2)))
        ==. Pg lc c m (TLabeledTCB ll THole)
        ==. Pg lc c m (εTerm l (TLabeledTCB ll t2))
        ==. ε l (Pg lc c m (TLabeledTCB ll t2))
        ==. ε l (evalProgram p)
        *** QED
        

simulations'' p@(Pg lc c m t@(TLabel t1@(TVLabel ll) t2)) l = 
        evalEraseProgram (ε l p) l
    ==. ε l (evalProgram (ε l p))
    ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
    ==. ε l (evalProgram (Pg lc c m (TLabel (εTerm l t1) (εTerm l t2))))
    ==. ε l (evalProgram (Pg lc c m (TLabel t1 (εTerm l t2))))
    ==. ε l (evalProgram (Pg lc c m TException))
    ==. ε l (evalProgram p)
    *** QED

simulations'' p@(Pg lc c m t@(TLabel t1 t2)) l | propagateException t = 
        evalEraseProgram (ε l p) l
    ==. ε l (evalProgram (ε l p))
    ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
    ==. ε l (evalProgram (Pg lc c m (TLabel (εTerm l t1) (εTerm l t2))))
    ==. ε l (Pg lc c m (eval (TLabel (εTerm l t1) (εTerm l t2))))
    ==. ε l (Pg lc c m (eval (εTerm l t)))
    ==. ε l (Pg lc c m TException) ? propagateErasePropagates l t
    ==. ε l (Pg lc c m (eval t))
    ==. ε l (evalProgram p)
    *** QED

simulations'' p@(Pg lc c m t@(TLabel t1 t2)) l = 
        evalEraseProgram (ε l p) l
    ==. ε l (evalProgram (ε l p))
    ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
    ==. ε l (evalProgram (Pg lc c m (TLabel (εTerm l t1) (εTerm l t2))))
    ==. ε l (Pg lc c m (eval (TLabel (εTerm l t1) (εTerm l t2))))
    ==. ε l (Pg lc c m (eval (εTerm l t)))
    ==. Pg lc c m (εTerm l (eval (εTerm l t)))
    ==. Pg lc c m (εTerm l (eval t))
        ? eraseEvalEraseSimulation l t
    ==. ε l (Pg lc c m (eval t))
    ==. ε l (evalProgram p)
    *** QED

simulations'' p@(Pg lc c m t@(TToLabeled t1 t2)) l | TVLabel ll <- t1 = 
    if lc `canFlowTo` ll && ll `canFlowTo` c then
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (evalProgram (Pg lc c m (TToLabeled (εTerm l t1) (εTerm l t2))))
        ==. ε l (evalProgram (Pg lc c m (TToLabeled (TVLabel ll) (εTerm l t2))))
        ==. ε l (if lc'' `canFlowTo` ll then Pg lc c m'' (TLabeledTCB ll t'') else Pg lc c m'' (TLabeledTCB ll TException))

        ==. ε l (if lc' `canFlowTo` ll then Pg lc c m' (TLabeledTCB ll t') else Pg lc c m' (TLabeledTCB ll TException)) ?
                terminationAxiomTToLabeled lc c m t1 t2 
            &&& simulationsStar'' (Pg lc c m t2) l
            &&& simulationsToLabeledHelper l lc lc' lc'' c c' c'' m m' m'' ll t2 t' t''
        ==. ε l (evalProgram p)
        *** QED
    else
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (evalProgram (Pg lc c m (TToLabeled (εTerm l t1) (εTerm l t2))))
        ==. ε l (evalProgram (Pg lc c m (TToLabeled (TVLabel ll) (εTerm l t2))))
        ==. ε l (Pg lc c m TException)
        ==. ε l (evalProgram p)
        *** QED

    where
        (Pg lc' c' m' t') = evalProgramStar (Pg lc c m t2)
        (Pg lc'' c'' m'' t'') = evalProgramStar (Pg lc c m (εTerm l t2))

simulations'' p@(Pg lc c m t@(TToLabeled t1 t2)) l = case propagateException t of
    True -> 
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (evalProgram (Pg lc c m (TToLabeled (εTerm l t1) (εTerm l t2))))
        ==. ε l (Pg lc c m (eval (TToLabeled (εTerm l t1) (εTerm l t2))))
        ==. ε l (Pg lc c m (eval (εTerm l t)))
        ==. ε l (Pg lc c m TException) ? propagateErasePropagates l t
        ==. ε l (Pg lc c m (eval t))
        ==. ε l (evalProgram p)
        *** QED
    False -> 
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l p))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (evalProgram (Pg lc c m (TToLabeled (εTerm l t1) (εTerm l t2))))
        ==. ε l (Pg lc c m (eval (TToLabeled (εTerm l t1) (εTerm l t2))))
        ==. ε l (Pg lc c m (eval (εTerm l t)))
        ==. Pg lc c m (εTerm l (eval (εTerm l t)))
        ==. Pg lc c m (εTerm l (eval t)) ? eraseEvalEraseSimulation l t
        ==. ε l (Pg lc c m (eval t))
        ==. ε l (evalProgram p)
        *** QED

simulations'' p@(Pg lc c m t@TGetLabel) l =
        evalEraseProgram (ε l p) l
    ==. ε l (evalProgram (ε l p))
    ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
    ==. ε l (evalProgram (Pg lc c m t))
    *** QED

simulations'' p@(Pg lc c m t@TGetClearance) l =
        evalEraseProgram (ε l p) l
    ==. ε l (evalProgram (ε l p))
    ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
    ==. ε l (evalProgram (Pg lc c m t))
    *** QED

simulations'' p@(Pg lc c m t@(TLabelOf t1)) l | propagateException t =
        evalEraseProgram (ε l p) l
    ==. ε l (evalProgram (ε l p))
    ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
    ==. ε l (evalProgram (Pg lc c m (TLabelOf (εTerm l t1))))
    ==. ε l (Pg lc c m (eval (TLabelOf (εTerm l t1))))
    ==. ε l (Pg lc c m (eval (εTerm l t)))
    ==. ε l (Pg lc c m TException) ? propagateErasePropagates l t
    ==. ε l (Pg lc c m (eval t))
    ==. ε l (evalProgram p)
    *** QED
    
simulations'' p@(Pg lc c m t@(TLabelOf t1')) l =
        evalEraseProgram (ε l p) l
    ==. ε l (evalProgram (ε l p))
    ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
    ==. ε l (evalProgram (Pg lc c m (TLabelOf (εTerm l t1'))))
    ==. ε l (Pg lc c m (eval (TLabelOf (εTerm l t1'))))
    ==. Pg lc c m (εTerm l (eval (TLabelOf (εTerm l t1'))))
    ==. Pg lc c m (εTerm l (eval (εTerm l t)))
    ==. Pg lc c m (εTerm l (eval t)) ? eraseEvalEraseSimulation l t
    ==. ε l (Pg lc c m (eval t))
    ==. ε l (evalProgram p)
    *** QED

simulations'' p@(Pg lc c m t@TException) l =
        evalEraseProgram (ε l p) l
    ==. ε l (evalProgram (ε l (Pg lc c m TException)))
    ==. ε l (evalProgram (Pg lc c m (εTerm l TException)))
    ==. ε l (evalProgram (Pg lc c m TException))
    ==. ε l (evalProgram p)
    *** QED

-- simulations'' p@(Pg lc c m t@THole) l =
--         evalEraseProgram (ε l p) l
--     ==. ε l (evalProgram (ε l (Pg lc c m t)))
--     ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
--     ==. ε l (evalProgram (Pg lc c m t))
--     ==. ε l (evalProgram p)
--     *** QED

simulations'' p@(Pg lc c m t@TTrue) l =
        evalEraseProgram (ε l p) l
    ==. ε l (evalProgram (ε l (Pg lc c m t)))
    ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
    ==. ε l (evalProgram (Pg lc c m t))
    ==. ε l (evalProgram p)
    *** QED

simulations'' p@(Pg lc c m t@TFalse) l =
        evalEraseProgram (ε l p) l
    ==. ε l (evalProgram (ε l (Pg lc c m t)))
    ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
    ==. ε l (evalProgram (Pg lc c m t))
    ==. ε l (evalProgram p)
    *** QED

simulations'' p@(Pg lc c m t@TUnit) l =
        evalEraseProgram (ε l p) l
    ==. ε l (evalProgram (ε l (Pg lc c m t)))
    ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
    ==. ε l (evalProgram (Pg lc c m t))
    ==. ε l (evalProgram p)
    *** QED

simulations'' p@(Pg lc c m t@(TVar _)) l =
        evalEraseProgram (ε l p) l
    ==. ε l (evalProgram (ε l (Pg lc c m t)))
    ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
    ==. ε l (evalProgram (Pg lc c m t))
    ==. ε l (evalProgram p)
    *** QED

simulations'' p@(Pg lc c m t@(TVLabel _)) l =
        evalEraseProgram (ε l p) l
    ==. ε l (evalProgram (ε l (Pg lc c m t)))
    ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
    ==. ε l (evalProgram (Pg lc c m t))
    ==. ε l (evalProgram p)
    *** QED

simulations'' p@(Pg lc c m t@(TLabeledTCB ll t1)) l =
    if ll `canFlowTo` l then
            evalEraseProgram (ε l p) l
        ==. ε l (evalProgram (ε l (Pg lc c m t)))
        ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==. ε l (evalProgram (Pg lc c m (TLabeledTCB ll (εTerm l t1))))
        ==. ε l (Pg lc c m (eval (TLabeledTCB ll (εTerm l t1))))
        ==. ε l (Pg lc c m (TLabeledTCB ll (εTerm l t1)))
        ==. Pg lc c m (εTerm l (TLabeledTCB ll (εTerm l t1)))
        ==. Pg lc c m (TLabeledTCB ll (εTerm l (εTerm l t1)))
        ==. Pg lc c m (TLabeledTCB ll (εTerm l t1)) ?
            εTermIdempotent l t1

        ==. Pg lc c m (εTerm l (TLabeledTCB ll t1))
        ==. ε l (Pg lc c m (TLabeledTCB ll t1))
        ==. ε l (Pg lc c m (eval t))
        ==. ε l (evalProgram (Pg lc c m t))
        ==. ε l (evalProgram p)
        *** QED
    else
        if lc `canFlowTo` l then
                evalEraseProgram (ε l p) l
            ==. ε l (evalProgram (ε l (Pg lc c m t)))
            ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
            ==. ε l (evalProgram (Pg lc c m (TLabeledTCB ll THole)))
            ==. ε l (Pg lc c m (eval (TLabeledTCB ll THole)))
            ==. ε l (Pg lc c m (TLabeledTCB ll THole))
            ==. Pg lc c m (εTerm l (TLabeledTCB ll THole))
            ==. Pg lc c m (TLabeledTCB ll THole)
            ==. Pg lc c m (εTerm l t)
            ==. ε l (Pg lc c m t)
            ==. ε l (Pg lc c m (eval t))
            ==. ε l (evalProgram p)
            *** QED
        else
                evalEraseProgram (ε l p) l
            ==. ε l (evalProgram (ε l (Pg lc c m t)))
            ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
            ==. ε l (evalProgram (Pg lc c m (TLabeledTCB ll THole)))
            ==. ε l (Pg lc c m (eval (TLabeledTCB ll THole)))
            ==. ε l (Pg lc c m (TLabeledTCB ll THole))
            ==. PgHole
            ==. ε l (Pg lc c m t)
            ==. ε l (Pg lc c m (eval t))
            ==. ε l (evalProgram p)
            *** QED

-- simulations'' p@(Pg lc c m t) l =
--         evalEraseProgram (ε l p) l
--     ==. ε l (evalProgram (ε l (Pg lc c m t)))
--     ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
--     ==. ε l (evalProgram (Pg lc c m t))
--     ==. ε l (evalProgram p)
--     *** QED

{-@ simulationsHoles'' 
 :: p : {Program | ς p} 
 -> {l : Label | not (canFlowTo (pLabel p) l)} 
 -> {v:Proof | evalEraseProgram (ε l p) l = PgHole} @-}
simulationsHoles'' :: Program -> Label -> Proof
simulationsHoles'' p@(Pg _ _ _ _) l =
        evalEraseProgram (ε l p) l
    ==. evalEraseProgram PgHole l
    ==. ε l (evalProgram PgHole)
    ==. ε l PgHole
    ==. PgHole
    *** QED

-- Simulations case when there are holes (current label exceeds output label).
{-@ simulationsHoles' 
  :: {p : Program | ς p && terminates p}
  -> {l : Label | not (canFlowTo (pLabel p) l)}
  -> {v:Proof | evalEraseProgram (ε l p) l = ε l (evalProgram p)} @-}

simulationsHoles' :: Program -> Label -> Proof
simulationsHoles' p@(Pg lc cc m (TBind t1 t2)) l = 
    let p1 = Pg lc cc m t1 in
    case evalProgramStar p1 of
        ps@(Pg l' c' m' t') -> 
                evalEraseProgram (ε l p) l
            ==. PgHole ? simulationsHoles'' p l
            ==. ε l (Pg l' c' m' (TApp t2 t')) ? (safeProgramBindsToSafeProgram p t1 t2 &&& terminationAxiomTBind lc cc m t1 t2 &&& monotonicLabelEvalProgramStar p1 &&& greaterLabelNotFlowTo lc l' l)
            ==. ε l (evalProgram p)
            *** QED
        PgHole ->
                evalEraseProgram (ε l p) l
            ==. PgHole ? simulationsHoles'' p l
            ==. ε l PgHole
            ==. ε l (evalProgram p)
            *** QED

simulationsHoles' p@(Pg lc cc m TGetLabel) l =
        evalEraseProgram (ε l p) l
    ==. PgHole ? simulationsHoles'' p l
    ==. ε l (Pg lc cc m (TVLabel lc))
    ==. ε l (Pg lc cc m (TVLabel lc))
    ==. ε l (evalProgram p)
    *** QED

simulationsHoles' p@(Pg lc cc m TGetClearance) l =
        evalEraseProgram (ε l p) l
    ==. PgHole ? simulationsHoles'' p l
    ==. ε l (Pg lc cc m (TVLabel cc))
    ==. ε l (Pg lc cc m (TVLabel cc))
    ==. ε l (evalProgram p)
    *** QED

simulationsHoles' p@(Pg lc cc m (TLowerClearance (TVLabel c'))) l | lc `canFlowTo` c' && c' `canFlowTo` cc = 
        evalEraseProgram (ε l p) l
    ==. PgHole ? simulationsHoles'' p l
    ==. ε l (Pg lc c' m TUnit)
    ==. ε l (evalProgram p)
    *** QED

simulationsHoles' p@(Pg lc cc m (TLowerClearance (TVLabel _c'))) l = 
        evalEraseProgram (ε l p) l
    ==. PgHole ? simulationsHoles'' p l
    ==. ε l (Pg lc cc m TException)
    ==. ε l (Pg lc cc m TException)
    ==. ε l (evalProgram p)
    *** QED

simulationsHoles' p@(Pg lc cc m (TLabel (TVLabel ll) t)) l | lc `canFlowTo` ll && ll `canFlowTo` cc =
        evalEraseProgram (ε l p) l
    ==. PgHole ? simulationsHoles'' p l
    ==. ε l (Pg lc cc m (TLabeledTCB ll t))
    ==. ε l (Pg lc cc m (TLabeledTCB ll t))
    ==. ε l (evalProgram p)
    *** QED

simulationsHoles' p@(Pg lc cc m (TLabel (TVLabel _ll) _)) l 
    =   evalEraseProgram (ε l p) l
    ==. PgHole ? simulationsHoles'' p l
    ==. ε l (Pg lc cc m TException)
    ==. ε l (Pg lc cc m TException)
    ==. ε l (evalProgram p)
    *** QED

simulationsHoles' p@(Pg lc cc m (TUnlabel (TLabeledTCB ll t))) l | (lc `join` ll) `canFlowTo` cc = 
        evalEraseProgram (ε l p) l
    ==. PgHole ? simulationsHoles'' p l
    ==. ε l (Pg (lc `join` ll) cc m t) ? joinLeftNotFlowTo l lc ll
    ==. ε l (Pg (lc `join` ll) cc m t)
    ==. ε l (evalProgram p)
    *** QED

simulationsHoles' p@(Pg lc cc m (TUnlabel (TLabeledTCB ll t))) l =
        evalEraseProgram (ε l p) l
    ==. PgHole ? simulationsHoles'' p l
    ==. (ε l (Pg lc cc m TException))
    ==. ε l (Pg lc cc m TException)
    ==. ε l (evalProgram p)
    *** QED

simulationsHoles' p@(Pg lc cc m (TToLabeled (TVLabel ll) t)) l | lc `canFlowTo` ll && ll `canFlowTo` cc = case evalProgramStar (Pg lc cc m t) of
    (Pg l' _ m' t') | l' `canFlowTo` ll ->
        -- if l' `canFlowTo` ll then
            evalEraseProgram (ε l p) l
        ==. PgHole ? simulationsHoles'' p l
        ==. ε l ((Pg lc cc m' (TLabeledTCB ll t')))
        ==. ε l (evalProgram p)
        *** QED
        -- else

    (Pg l' _ m' t') ->
            evalEraseProgram (ε l p) l
        ==. PgHole ? simulationsHoles'' p l
        ==. ε l ((Pg lc cc m' (TLabeledTCB ll TException)))
        ==. ε l (evalProgram p)
        *** QED

    PgHole ->
        unreachable

simulationsHoles' p@(Pg lc cc m (TToLabeled (TVLabel _ll) _t)) l = 
        evalEraseProgram (ε l p) l
    ==. PgHole ? simulationsHoles'' p l
    ==. ε l (Pg lc cc m TException)
    ==. ε l (Pg lc cc m TException)
    ==. ε l (evalProgram p)
    *** QED

simulationsHoles' p@(Pg lc cc m t) l = 
    let t' = eval t in
        evalEraseProgram (ε l p) l
    ==. PgHole ? simulationsHoles'' p l
    ==. ε l (Pg lc cc m t')
    ==. ε l (Pg lc cc m t')
    ==. ε l (Pg lc cc m (eval t))
    ==. ε l (evalProgram p)
    *** QED

simulationsHoles' PgHole l =
        evalEraseProgram (ε l PgHole) l
    ==. PgHole ? simulationsHoles'' PgHole l
    ==. ε l (evalProgram PgHole)
    *** QED

{-@ eraseJoinLeft 
 :: l:Label 
 -> lc:{Label | not (canFlowTo lc l)} 
 -> ll:Label
 -> cc:Label 
 -> m:Memory
 -> t:Term
 -> v:{Proof | ε l (Pg (join lc ll) cc m t) = PgHole} 
@-}
eraseJoinLeft :: Label -> Label -> Label -> Label -> Memory -> Term -> Proof
eraseJoinLeft l lc ll cc m t = 
        ε l (Pg (join lc ll) cc m t) ==. PgHole ? joinLeftNotFlowTo l lc ll
    *** QED

{-@ simulationsToLabeledHelper
 :: l : Label
 -> lc : {Label | canFlowTo lc l}
 -> lc' : Label
 -> lc'' : Label
 -> c : Label
 -> c' : Label
 -> c'' : Label
 -> m : Memory
 -> m' : Memory
 -> m'' : Memory
 -> ll : Label
 -> t : {Term | ε l (evalProgramStar (ε l (Pg lc c m t))) = ε l (evalProgramStar (Pg lc c m t)) && terminates (Pg lc c m t)}
 -> t' : {Term | Pg lc' c' m' t' = evalProgramStar (Pg lc c m t)}
 -> t'' : {Term | Pg lc'' c'' m'' t'' = evalProgramStar (Pg lc c m (εTerm l t))}
 -> {ε l (if (canFlowTo lc' ll) then (Pg lc c m' (TLabeledTCB ll t')) else (Pg lc c m' (TLabeledTCB ll TException))) = ε l (if (canFlowTo lc'' ll) then (Pg lc c m'' (TLabeledTCB ll t'')) else Pg lc c m'' (TLabeledTCB ll TException))}
 / [evalSteps (Pg lc c m t), 4]
 @-}
simulationsToLabeledHelper :: Label -> Label -> Label -> Label -> Label -> Label -> Label -> Memory -> Memory -> Memory -> Label -> Term -> Term -> Term -> Proof
simulationsToLabeledHelper l lc lc' lc'' c c' c'' m m' m'' ll t t' t'' | ll `canFlowTo` l = case ( lc' `canFlowTo` l, lc'' `canFlowTo` l) of
    (True, True) -> 
            ε l (if (canFlowTo lc' ll) then (Pg lc c m' (TLabeledTCB ll t')) else (Pg lc c m' (TLabeledTCB ll TException)))
        ==. ε l (Pg lc c m' (TLabeledTCB ll (if canFlowTo lc' ll then t' else TException)))
        ==. Pg lc c m' (εTerm l (TLabeledTCB ll (if canFlowTo lc' ll then t' else TException)))
        ==. Pg lc c m' (TLabeledTCB ll (εTerm l (if canFlowTo lc' ll then t' else TException)))
        ==. Pg lc c m' (TLabeledTCB ll (if canFlowTo lc' ll then (εTerm l t') else (εTerm l TException)))
        ==. Pg lc c m' (TLabeledTCB ll (if canFlowTo lc' ll then (εTerm l t') else TException))

        ==. Pg lc c m'' (TLabeledTCB ll (if canFlowTo lc'' ll then (εTerm l t'') else TException)) ? 
            (   Pg lc' c' m' (εTerm l t')
            ==. ε l (Pg lc' c' m' t')
            ==. ε l (evalProgramStar (Pg lc c m t))
            ==. ε l (evalProgramStar (ε l (Pg lc c m t)))
            ==. ε l (evalProgramStar (Pg lc c m (εTerm l t)))
            ==. ε l (Pg lc'' c'' m'' t'')
            ==. Pg lc'' c'' m'' (εTerm l t'')
            *** QED
            )
        ==. Pg lc c m'' (TLabeledTCB ll (if canFlowTo lc'' ll then (εTerm l t'') else (εTerm l TException)))
        ==. Pg lc c m'' (TLabeledTCB ll (εTerm l (if canFlowTo lc'' ll then t'' else TException)))
        ==. Pg lc c m'' (εTerm l (TLabeledTCB ll (if canFlowTo lc'' ll then t'' else TException)))
        ==. ε l (Pg lc c m'' (TLabeledTCB ll (if canFlowTo lc'' ll then t'' else TException)))
        ==. ε l (if (canFlowTo lc'' ll) then (Pg lc c m'' (TLabeledTCB ll t'')) else Pg lc c m'' (TLabeledTCB ll TException))
        *** QED

    (True, False) ->
        -- this case is unreachable
        -- lc'' < lc'
        -- lc' < l && not (lc'' < l) 
        -- lc'' < lc' < l && lc'' > l

        --     erasedStarCanFlowTo (Pg lc c m t) l
        -- &&& assert (lc'' `canFlowTo` lc')

        -- Contradiction
        
            Pg lc' c' m' (εTerm l t')
        ==. ε l (Pg lc' c' m' t')
        ==. ε l (evalProgramStar (Pg lc c m t))
        ==. ε l (evalProgramStar (ε l (Pg lc c m t)))
        ==. ε l (evalProgramStar (Pg lc c m (εTerm l t)))
        ==. ε l (Pg lc'' c'' m'' t'')
        ==. PgHole
        *** QED

    (False, False) -> -- Implies lc' > l, lc'' > l
            ε l (if (canFlowTo lc' ll) then (Pg lc c m' (TLabeledTCB ll t')) else (Pg lc c m' (TLabeledTCB ll TException)))
        ==. ε l (Pg lc c m' (TLabeledTCB ll (if canFlowTo lc' ll then t' else TException)))
        ==. ε l (Pg lc c m' (TLabeledTCB ll TException))
        ==. ε l (Pg lc c m'' (TLabeledTCB ll TException))
        ==. ε l (Pg lc c m'' (TLabeledTCB ll (if canFlowTo lc'' ll then t'' else TException)))
        ==. ε l (if (canFlowTo lc'' ll) then (Pg lc c m'' (TLabeledTCB ll t'')) else Pg lc c m'' (TLabeledTCB ll TException))
        *** QED

    (False, True) -> -- Implies lc'' > l
        -- Contradiction

            PgHole
        ==. ε l (Pg lc' c' m' t')
        ==. ε l (evalProgramStar (Pg lc c m t))
        ==. ε l (evalProgramStar (ε l (Pg lc c m t)))
        ==. ε l (evalProgramStar (Pg lc c m (εTerm l t)))
        ==. ε l (Pg lc'' c'' m'' t'')
        ==. Pg lc'' c'' m'' (εTerm l t'')
        *** QED

simulationsToLabeledHelper l lc lc' lc'' c c' c'' m m' m'' ll t t' t'' = 
        ε l (if (canFlowTo lc' ll) then (Pg lc c m' (TLabeledTCB ll t')) else (Pg lc c m' (TLabeledTCB ll TException)))
    ==. ε l (Pg lc c m' (TLabeledTCB ll (if canFlowTo lc' ll then t' else TException)))
    ==. Pg lc c m' (εTerm l (TLabeledTCB ll (if canFlowTo lc' ll then t' else TException)))
    ==. Pg lc c m' (εTerm l (TLabeledTCB ll THole))
    ==. Pg lc c m'' (εTerm l (TLabeledTCB ll (if canFlowTo lc'' ll then t'' else TException)))
    ==. ε l (Pg lc c m'' (TLabeledTCB ll (if canFlowTo lc'' ll then t'' else TException)))
    ==. ε l (if (canFlowTo lc'' ll) then (Pg lc c m'' (TLabeledTCB ll t'')) else Pg lc c m'' (TLabeledTCB ll TException))
    *** QED


valueEterm :: Label -> Term -> Proof
{-@ valueEterm :: l:Label -> t:Term -> {v:Proof | isValue t <=> isValue (εTerm l t) } @-}
valueEterm l t@THole = 
        isValue t
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@(TLam v t1) =
        isValue t
    ==. isValue (TLam v (εTerm l t1))
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@TTrue =
        isValue t
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@TFalse =
        isValue t
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@TUnit =
        isValue t
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@(TVar _) =
        isValue t
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@(TApp t1 t2) =
        isValue t
    ==. isValue (TApp (εTerm l t1) (εTerm l t2))
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@(TFix t1) =
        isValue t
    ==. isValue (TFix (εTerm l t1))
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@(TIf t1 t2 t3) =
        isValue t
    ==. isValue (TIf (εTerm l t1) (εTerm l t2) (εTerm l t3))
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@(TVLabel _) =
        isValue t
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@(TJoin t1 t2) =
        isValue t
    ==. isValue (TJoin (εTerm l t1) (εTerm l t2))
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@(TMeet t1 t2) =
        isValue t
    ==. isValue (TMeet (εTerm l t1) (εTerm l t2))
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@(TCanFlowTo t1 t2) =
        isValue t
    ==. isValue (TCanFlowTo (εTerm l t1) (εTerm l t2))
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@(TBind t1 t2) =
        isValue t
    ==. isValue (TBind (εTerm l t1) (εTerm l t2))
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@TGetLabel =
        isValue t
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@TGetClearance =
        isValue t
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@(TLowerClearance t1) =
        isValue t
    ==. isValue (TLowerClearance (εTerm l t1))
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@(TLabeledTCB ll t1) | ll `canFlowTo` l =
        isValue t
    ==. isValue (TLabeledTCB ll (εTerm l t1))
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@(TLabeledTCB ll t1) =
        isValue t
    ==. isValue (TLabeledTCB ll THole)
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@(TLabelOf t1) =
        isValue t
    ==. isValue (TLabelOf (εTerm l t1))
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@(TLabel t1 t2) =
        isValue t
    ==. isValue (TLabel (εTerm l t1) (εTerm l t2))
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@(TUnlabel t1) =
        isValue t
    ==. isValue (TUnlabel (εTerm l t1))
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@(TToLabeled t1 t2) =
        isValue t
    ==. isValue (TToLabeled (εTerm l t1) (εTerm l t2))
    ==. isValue (εTerm l t)
    *** QED

valueEterm l t@TException =
        isValue t
    ==. isValue (εTerm l t)
    *** QED

{-@ simulationsTBind :: l:Label -> lc:{Label | canFlowTo lc l} -> c:Label -> m:Memory -> t1:Term -> t2:{Term | terminates (Pg lc c m (TBind t1 t2)) } 
 -> {v : Proof | ε l (evalProgram (Pg lc c m (TBind (εTerm l t1) (εTerm l t2)))) == ε l (evalProgram (Pg lc c m (TBind t1 t2))) }
 / [evalSteps (Pg lc c m (TBind t1 t2)), 0]
 @-}

simulationsTBind :: Label -> Label -> Label -> Memory -> Term -> Term -> Proof 

simulationsTBind l lc c m t1 t2 
  | l'' `canFlowTo` l, l' `canFlowTo` l 
  =   ε l (evalProgram (Pg lc c m (TBind (εTerm l t1) (εTerm l t2))))
  ==. ε l (Pg l' c' m' (TApp (εTerm l t2) t')) 
  ==. Pg l' c' m' (εTerm l (TApp (εTerm l t2) t')) 
  ==. Pg l' c' m' (TApp (εTerm l (εTerm l t2)) (εTerm l t')) 
  ==. Pg l' c' m' (TApp (εTerm l t2) (εTerm l t')) ? εTermIdempotent l t2  
  ==. Pg l' c' m' (TApp (εTerm l t2) (εTerm l t')) ? 
        (     Pg l' c' m' (εTerm l t')
          ==. ε l (Pg l' c' m' t')
          ==. ε l (evalProgramStar (Pg lc c m (εTerm l t1)))
          ==. ε l (evalProgramStar (ε l (Pg lc c m t1)))
          ==. ε l (evalProgramStar (Pg lc c m t1)) 
              ? terminationAxiomTBind lc c m t1 t2 &&& simulationsStar'' (Pg lc c m t1) l 
          ==. ε l (Pg l'' c'' m'' t'')
          ==. Pg l'' c'' m'' (εTerm l t'')
          *** QED 
        )
  ==. Pg l'' c'' m'' (TApp (εTerm l t2) (εTerm l t''))
  ==. Pg l'' c'' m'' (εTerm l (TApp t2 t''))
  ==. ε l (Pg l'' c'' m'' (TApp t2 t''))
  ==. ε l (evalProgram (Pg lc c m (TBind t1 t2)))
  *** QED 
  | not (l'' `canFlowTo` l), not (l' `canFlowTo` l) 
  =   ε l (evalProgram (Pg lc c m (TBind (εTerm l t1) (εTerm l t2))))
  ==. ε l (Pg l' c' m' (TApp (εTerm l t2) t')) 
  ==. PgHole 
  ==. ε l (Pg l'' c'' m'' (TApp t2 t''))
  ==. ε l (evalProgram (Pg lc c m (TBind t1 t2)))
  *** QED 
  | not (l'' `canFlowTo` l),  l' `canFlowTo` l
  =   Pg l' c' m' (εTerm l t')
  ==. ε l (Pg l' c' m' t')
  ==. ε l (evalProgramStar (Pg lc c m (εTerm l t1)))
  ==. ε l (evalProgramStar (ε l (Pg lc c m t1)))
  ==. ε l (evalProgramStar (Pg lc c m t1)) 
      ? terminationAxiomTBind lc c m t1 t2 &&& simulationsStar'' (Pg lc c m t1) l 
  ==. ε l (Pg l'' c'' m'' t'')
  ==. PgHole
  *** QED 
  | l'' `canFlowTo` l, not (l' `canFlowTo` l)
  =   PgHole
  ==. ε l (Pg l' c' m' t')
  ==. ε l (evalProgramStar (Pg lc c m (εTerm l t1)))
  ==. ε l (evalProgramStar (ε l (Pg lc c m t1)))
  ==. ε l (evalProgramStar (Pg lc c m t1)) 
      ? terminationAxiomTBind lc c m t1 t2 &&& simulationsStar'' (Pg lc c m t1) l 
  ==. ε l (Pg l'' c'' m'' t'')
  ==. Pg l'' c'' m'' (εTerm l t'')
  *** QED 
   where
    Pg l' c' m' t'     = evalProgramStar (Pg lc c m (εTerm l t1))
    Pg l'' c'' m'' t'' = evalProgramStar (Pg lc c m t1)


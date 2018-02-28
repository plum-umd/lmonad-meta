{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}

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

import ProofCombinators

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

{-@ simulations'' 
 :: {p : Program | ς p} 
 -> {l : Label | canFlowTo (pLabel p) l}
 -> {v : Proof | evalEraseProgram (ε l p) l = ε l (evalProgram p)}
 @-}
simulations'' :: Program -> Label -> Proof
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
    undefined
    --     evalEraseProgram (ε l p) l
    -- ==! ε l (evalProgram (ε l p))
    -- ==! ε l (evalProgram (Pg lc c m (εTerm l t)))
    -- ==! ε l (evalProgram (Pg lc c m (TBind (εTerm l t1) (εTerm l t2))))
    -- ==! ε l (Pg l'' c'' m'' (TApp (εTerm l t2) t''))

    -- -- ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
    -- -- ==. ε l (evalProgram (ε l (Pg lc c m t)))

    -- ==! ε l (Pg l' c' m' (TApp t2 t'))
    -- ==! ε l (evalProgram (Pg lc c m (TBind t1 t2)))
    -- ==! ε l (evalProgram p)
    -- *** QED

    -- where
    --     (Pg l' c' m' t') = evalProgramStar (Pg lc c m t1)
    --     (Pg l'' c'' m'' t'') = evalProgramStar (Pg lc c m (εTerm l t1))

simulations'' p@(Pg lc c m t@(TLowerClearance (TVLabel c'))) l =
        evalEraseProgram (ε l p) l
    ==! ε l (evalProgram (ε l p))
    ==! ε l (evalProgram (Pg lc c m (εTerm l t)))
    ==! ε l (evalProgram (Pg lc c m (TLowerClearance (εTerm l (TVLabel c')))))
    ==! ε l (evalProgram (Pg lc c m (TLowerClearance (TVLabel c'))))
    ==! ε l (evalProgram p)
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
        ==! ε l (evalProgram (ε l p))
        ==! ε l (evalProgram (Pg lc c m (εTerm l t)))
        ==! ε l (evalProgram (Pg lc c m (TLowerClearance (εTerm l t1))))
        ==: ε l (Pg lc c m (eval (TLowerClearance (εTerm l t1)))) ? eraseNotTVLabel l t1
        ==! ε l (Pg lc c m (eval (εTerm l t)))
        ==! Pg lc c m (εTerm l (eval (εTerm l t)))
        ==: Pg lc c m (εTerm l (eval t)) ? eraseEvalEraseSimulation l t
        ==! ε l (Pg lc c m (eval t))
        ==! ε l (evalProgram p)
        *** QED

simulations'' p@(Pg lc c m t@(TUnlabel _)) l = undefined
simulations'' p@(Pg lc c m t@(TLabel _ _)) l = undefined
simulations'' p@(Pg lc c m t@(TLabeledTCB _ _)) l = undefined
simulations'' p@(Pg lc c m t@(TLabelOf _)) l = undefined
simulations'' p@(Pg lc c m t@(TToLabeled _ _)) l = undefined
simulations'' p@(Pg lc c m t@TException) l = undefined
simulations'' p@(Pg lc c m t) l = -- undefined
        evalEraseProgram (ε l p) l
    ==. ε l (evalProgram (Pg lc c m (εTerm l t)))
    ==. ε l (evalProgram (ε l (Pg lc c m t)))
    *** QED

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


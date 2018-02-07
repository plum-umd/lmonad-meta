{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}
{-@ LIQUID "--trustinternals"                           @-}

{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
module Simulations.Helpers where

import Label
import Language
import Programs 
import MetaFunctions

import ProofCombinators


{-@ pgTheorem :: {p:Program | isPg p } -> {isPg (evalProgram p) } @-}
pgTheorem :: Program -> Proof 
pgTheorem PgHole = unreachable
pgTheorem p@(Pg l c m (TBind t1 t2)) = 
    let p' = Pg l c m t1 in
    let p''@(Pg l' c' m' t') = evalProgramStar p' in
        isPg (evalProgram p)
    ==! isPg (Pg l' c' m' (TApp t2 t'))
    ==! True
    *** QED

pgTheorem p@(Pg l c m (TToLabeled (TVLabel ll) t)) | l `canFlowTo` ll && ll `canFlowTo` c = 
    let p' = Pg l c m t in
    let p''@(Pg l' c' m' t') = evalProgramStar p' in
    if l' `canFlowTo` ll then
            isPg (evalProgram p)
        ==! isPg (Pg l c m' (TLabeledTCB ll t'))
        ==! True
        *** QED
    else
            isPg (evalProgram p)
        ==! isPg (Pg l c m' (TLabeledTCB ll TException))
        ==! True
        *** QED
    
pgTheorem p =
    let p'@(Pg l' c' m' t') = evalProgram p in
        isPg (evalProgram p)
    ==! isPg p'
    ==! True
    *** QED


{-@ safeProgramBindsToSafeProgram 
 :: {p : Program | ς p}
 -> t1 : Term
 -> {t2 : Term | (TBind t1 t2) = pTerm p}
 -> {v:Proof | ς (Pg (pLabel p) (pClearance p) (pMemory p) t1)}
 @-}
safeProgramBindsToSafeProgram :: Program -> Term -> Term -> Proof
safeProgramBindsToSafeProgram p@(Pg l c m tb@(TBind t1 t2)) t1' t2' | t1 == t1' && t2 == t2' = 
    let p' = Pg l c m t1 in
        ς p'
    ==. ςTerm t1
    ==. ςTerm tb
    ==. True
    *** QED

{-@ safeProgramStarEvalsToNonHole
 :: {p : Program | ς p}
 -> {v : Proof | isPg (evalProgramStar p)}
 @-}
safeProgramStarEvalsToNonHole :: Program -> Proof
safeProgramStarEvalsToNonHole p = case evalProgramStar p of
    p'@(Pg _ _ _ t) -> -- | isValue t ->
            isPg (evalProgramStar p)
        ==. isPg p'
        ==. True
        *** QED

    PgHole ->
        unreachable

-- {-@ automatic-instances safeProgramEvalsToNonHole @-}
{-@ safeProgramEvalsToNonHole
 :: {p : Program | ς p}
 -> {v : Proof | isPg (evalProgram p)}
 @-}
safeProgramEvalsToNonHole :: Program -> Proof
safeProgramEvalsToNonHole PgHole = unreachable
safeProgramEvalsToNonHole p@(Pg _ _ _ t@(TLabeledTCB _ _)) = unreachable
safeProgramEvalsToNonHole p@(Pg l c m (TBind t1 _)) = case evalProgram p of
    p'@PgHole ->
        let p1 = Pg l c m t1 in
            False
        ==. isPg PgHole
        ==. isPg p'
        ==. isPg (evalProgram p)
        ==. isPg (evalProgramStar p1)
        ==. True ? safeProgramStarEvalsToNonHole p1
        *** QED
        
    p'@(Pg _ _ _ _) -> 
            isPg p'
        ==. True
        *** QED


safeProgramEvalsToNonHole p@(Pg _ _ _ _) = 
    let p'@(Pg _ _ _ _) = evalProgram p in
        isPg p'
    ==. True
    *** QED

-- JP: Move to Simulations.Language
{-@ propagateErasePropagates 
 :: l : Label
 -> t : {Term | propagateException t}
 -> {propagateException (εTerm l t)}
 / [size t]
 @-}
propagateErasePropagates :: Label -> Term -> Proof
propagateErasePropagates l t@TException = 
        propagateException (εTerm l t)
    ==! propagateException t
    *** QED

--         eval (εTerm l t)
--     ==! eval t
--     ==! TException
--     *** QED

propagateErasePropagates l t@(TLam v t1) = 
        propagateException (εTerm l t)
    ==! propagateException (TLam v (εTerm l t1))
    ==: True ? propagateErasePropagates l t1
    *** QED 

propagateErasePropagates l t@(TApp t1 t2) =
        propagateException (εTerm l t)
    ==! propagateException (TApp (εTerm l t1) (εTerm l t2))
    ==: True ? propagateErasePropagates l t1 &&& propagateErasePropagates l t2
    *** QED

propagateErasePropagates l t@(TFix t1) = 
        propagateException (εTerm l t)
    ==! propagateException (TFix (εTerm l t1))
    ==: True ? propagateErasePropagates l t1
    *** QED 

propagateErasePropagates l t@(TIf t1 t2 t3) = 
        propagateException (εTerm l t)
    ==! propagateException (TIf (εTerm l t2) (εTerm l t2) (εTerm l t3))
    ==: True ? propagateErasePropagates l t1 &&& propagateErasePropagates l t2 &&& propagateErasePropagates l t3
propagateErasePropagates l t@(TLabeledTCB _ _) = unreachable

propagateErasePropagates l t@(TLabel (TVLabel l') t2) | l' `canFlowTo` l =
        propagateException (εTerm l t)
    ==! propagateException (TLabel (TVLabel l') (εTerm l t2))
    ==: True ? propagateErasePropagates l t2
    *** QED

propagateErasePropagates l t@(TLabel (TVLabel l') t2) = admitted 
-- JP: I think εTerm for TLabel is wrong. It should never THole?

--         propagateException (εTerm l t)
--     ==! propagateException (TLabel (TVLabel l') THole)
--     ==! False
--     *** QED

propagateErasePropagates l t@(TLabel t1 t2) =
        propagateException (εTerm l t)
    ==! propagateException (TLabel (εTerm l t1) (εTerm l t2))
    ==: True ? propagateErasePropagates l t1 &&& propagateErasePropagates l t2
    *** QED

--         propagateException (εTerm l t)

-- (TVLabel l') t2) | l' `canFlowTo` l = 
--         propagateException (εTerm l t)
--     ==! propagateException (TLabel (TVLabel l') (εTerm l t2))
propagateErasePropagates l t@THole = unreachable
propagateErasePropagates l t = undefined


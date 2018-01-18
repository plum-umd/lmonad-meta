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


{-@ safeTheorem :: {p:Program | ς p } -> {ς (evalProgram p) } @-}
safeTheorem :: Program -> Proof 
safeTheorem _ = undefined 

{-@ jamesDoThat :: l1:Label -> l2:Label -> { canFlowTo l1 l2 } @-} 
jamesDoThat :: Label -> Label -> Proof 
jamesDoThat _ _ = undefined 


relfexiveLabel :: Label -> Proof
{-@ relfexiveLabel :: l:Label -> {canFlowTo l l} @-}
relfexiveLabel LabelA      = canFlowTo LabelA LabelA *** QED 
relfexiveLabel LabelB      = canFlowTo LabelB LabelB *** QED 
relfexiveLabel LabelAJoinB = canFlowTo LabelAJoinB LabelAJoinB *** QED 
relfexiveLabel LabelAMeetB = canFlowTo LabelAMeetB LabelAMeetB *** QED 


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



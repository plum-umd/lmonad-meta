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
 :: n : Index
 -> {p : Program | ς p}
 -> {p' : Program | p' = pSnd (evalProgramStar (Pair n p))}
 -> {v : Proof | isNotHole p'}
 @-}
safeProgramStarEvalsToNonHole :: Index -> Program -> Program -> Proof
safeProgramStarEvalsToNonHole _ _ _ = undefined

-- {-@ automatic-instances safeProgramEvalsToNonHole @-}
{-@ safeProgramEvalsToNonHole
 :: {p : Program | ς p}
 -> {v : Proof | isNotHole (pSnd (evalProgram p))}
 @-}
safeProgramEvalsToNonHole :: Program -> Proof
safeProgramEvalsToNonHole PgHole = unreachable
safeProgramEvalsToNonHole p@(Pg _ _ _ t@(TLabeledTCB _ _)) = unreachable
safeProgramEvalsToNonHole p@(Pg l c m (TBind t1 _)) = case evalProgram p of
    (Pair _ p'@PgHole) ->
            isNotHole p'
        ==! isNotHole (pSnd (evalProgram p))
        ==! isNotHole (pSnd (evalProgramStar (Pair 0 (Pg l c m t1))))
        ==: True ? safeProgramStarEvalsToNonHole 0 p p'
        -- -- ==. isNotHole 
        -- ==: True ? safeProgramStarEvalsToNonHole 0 p
        *** QED
        
    (Pair _ p'@(Pg _ _ _ _)) -> 
            isNotHole p'
        ==. True
        *** QED


safeProgramEvalsToNonHole p@(Pg _ _ _ _) = 
    let (Pair _ p'@(Pg _ _ _ _)) = evalProgram p in
        isNotHole p'
    ==. True
    *** QED


-- safeProgramEvalsToNonHole p@(Pg _ _ _ (TBind _ _)) = undefined
-- safeProgramEvalsToNonHole p@(Pg _ _ _ TGetLabel) = 
--     let (Pair 0 p'@(Pg _ _ _ (TVLabel l))) = evalProgram p in
--         isNotHole p'
--     ==. True
--     *** QED
-- 
-- safeProgramEvalsToNonHole p@(Pg _ _ _ TGetClearance) = 
--     let (Pair 0 p'@(Pg _ _ _ (TVLabel l))) = evalProgram p in
--         isNotHole p'
--     ==. True
--     *** QED
-- 
-- safeProgramEvalsToNonHole p@(Pg l c _ (TLowerClearance (TVLabel c'))) | l `canFlowTo` c' && c' `canFlowTo` c =
--     let (Pair 0 p'@(Pg _ _ _ TUnit)) = evalProgram p in
--         isNotHole p'
--     ==. True
--     *** QED
-- 
-- safeProgramEvalsToNonHole p@(Pg _ _ _ (TLowerClearance (TVLabel _))) =
--     let (Pair 0 p'@(Pg _ _ _ TException)) = evalProgram p in
--         isNotHole p'
--     ==. True
--     *** QED
-- 
-- safeProgramEvalsToNonHole p@(Pg l c _ (TLabel (TVLabel ll) _)) | l `canFlowTo` ll && ll `canFlowTo` c =
--     let (Pair 0 p'@(Pg _ _ _ (TLabeledTCB a b))) = evalProgram p in
--         isNotHole p'
--     ==. True
--     *** QED
-- 
-- safeProgramEvalsToNonHole p@(Pg _ _ _ (TLabel _ _)) =
--     let (Pair 0 p'@(Pg _ _ _ _)) = evalProgram p in
--         isNotHole p'
--     ==. True
--     *** QED
-- 
-- safeProgramEvalsToNonHole p@(Pg _ _ _ (TUnlabel _)) = undefined
-- safeProgramEvalsToNonHole p@(Pg _ _ _ (TToLabeled _ _)) = undefined
-- safeProgramEvalsToNonHole p@(Pg _ _ _ t) = undefined

    


-- {-@ automatic-instances monotonicLabelEvalProgram @-}
{-@ monotonicLabelEvalProgram
 :: {p : Program | ς p}
 -> {v : Proof | canFlowTo (pLabel p) (pLabel (pSnd (evalProgram p)))}
 @-}
monotonicLabelEvalProgram :: Program -> Proof
monotonicLabelEvalProgram p@(Pg l c m (TBind t1 t2)) = case evalProgram p of
    (Pair n p'@PgHole) ->
        safeProgramEvalsToNonHole p
    (Pair n (Pg l' c' m' t)) ->
        let pInter = Pg l c m t1 in
            canFlowTo l l'
        ==. True ? safeProgramBindsToSafeProgram p t1 t2 &&& monotonicLabelEvalProgramStar 0 pInter
        *** QED

monotonicLabelEvalProgram p@(Pg l c m TGetLabel) = -- 0 (Pg l' c' m' (TVLabel l'')) = 
    let (Pair 0 (Pg l' c' m' (TVLabel l''))) = evalProgram p in
        canFlowTo l l'
    ==. True
    *** QED

monotonicLabelEvalProgram p@(Pg l c m TGetClearance) =
    let (Pair 0 (Pg l' c' m' (TVLabel l''))) = evalProgram p in
        canFlowTo l l'
    ==. True
    *** QED

monotonicLabelEvalProgram p@(Pg l c m (TLowerClearance (TVLabel c'))) =
    let (Pair 0 (Pg l' c' m' t)) = evalProgram p in
        canFlowTo l l'
    ==. True
    *** QED

monotonicLabelEvalProgram p@(Pg l c m (TLabel (TVLabel ll) t)) =
    let (Pair 0 (Pg l' c' m' t)) = evalProgram p in
        canFlowTo l l'
    ==. True
    *** QED

monotonicLabelEvalProgram p@(Pg l c m (TUnlabel (TLabeledTCB ll t))) | l `join` ll `canFlowTo` c =
    let (Pair 0 (Pg l' c' m' t)) = evalProgram p in
        canFlowTo l l'
    ==. True
    *** QED

monotonicLabelEvalProgram p@(Pg l c m (TUnlabel (TLabeledTCB ll t))) =
    let (Pair 0 (Pg l' c' m' t)) = evalProgram p in
        canFlowTo l l'
    ==. True
    *** QED

monotonicLabelEvalProgram p@(Pg l c m (TToLabeled (TVLabel _) _)) =
    let (Pair n (Pg l' c' m' t)) = evalProgram p in
        canFlowTo l l'
    ==. True
    *** QED

monotonicLabelEvalProgram p@(Pg l c m t) = 
    let (Pair 0 (Pg l' c' m' t)) = evalProgram p in
        canFlowTo l l'
    ==. True
    *** QED

{-@ monotonicLabelEvalProgramStar
 :: n : Index
 -> {p : Program | ς p}
 -> {v : Proof | canFlowTo (pLabel p) (pLabel (pSnd (evalProgramStar (Pair n p))))}
 @-}
monotonicLabelEvalProgramStar :: Index -> Program -> Proof
monotonicLabelEvalProgramStar n p =
    undefined
    -- TODO: Unimplemented XXX

-- {-@ monotonicLabelEvalProgramStar
--  :: n : Index
--  -> p : Program
--  -> n' : Index
--  -> {p' : Program | evalProgramStar (Pair n p) == (Pair n' p')}
--  -> {v : Proof | canFlowTo (pLabel p) (pLabel p')}
--  @-}
-- monotonicLabelEvalProgramStar :: Index -> Program -> Index -> Program -> Proof
-- monotonicLabelEvalProgramStar n p n' p' =
--     -- TODO: Unimplemented XXX
-- 

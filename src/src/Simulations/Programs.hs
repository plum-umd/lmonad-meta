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
-- 
--         let (Pair n' p') = evalProgram p in
--         let (Pair n'' p'') = evalProgramStar (evalProgram p) in
--             isPg (pSnd (evalProgramStar (Pair n p)))
--         ==! isPg (pSnd (Pair (n + n') p''))
--         -- ==! isPg (pSnd (Pair (n + n') p'))
--         ==! isPg p'
--         -- ==! isPg (pSnd (evalProgramStar (Pair n' p')))
--         ==: True ? safeProgramStarEvalsToNonHole n' p'
--         *** QED

-- {-@ automatic-instances safeProgramEvalsToNonHole @-}
{-@ safeProgramEvalsToNonHole
 :: {p : Program | ς p}
 -> {v : Proof | isPg (pSnd (evalProgram p))}
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


-- safeProgramEvalsToNonHole p@(Pg _ _ _ (TBind _ _)) = undefined
-- safeProgramEvalsToNonHole p@(Pg _ _ _ TGetLabel) = 
--     let (Pair 0 p'@(Pg _ _ _ (TVLabel l))) = evalProgram p in
--         isPg p'
--     ==. True
--     *** QED
-- 
-- safeProgramEvalsToNonHole p@(Pg _ _ _ TGetClearance) = 
--     let (Pair 0 p'@(Pg _ _ _ (TVLabel l))) = evalProgram p in
--         isPg p'
--     ==. True
--     *** QED
-- 
-- safeProgramEvalsToNonHole p@(Pg l c _ (TLowerClearance (TVLabel c'))) | l `canFlowTo` c' && c' `canFlowTo` c =
--     let (Pair 0 p'@(Pg _ _ _ TUnit)) = evalProgram p in
--         isPg p'
--     ==. True
--     *** QED
-- 
-- safeProgramEvalsToNonHole p@(Pg _ _ _ (TLowerClearance (TVLabel _))) =
--     let (Pair 0 p'@(Pg _ _ _ TException)) = evalProgram p in
--         isPg p'
--     ==. True
--     *** QED
-- 
-- safeProgramEvalsToNonHole p@(Pg l c _ (TLabel (TVLabel ll) _)) | l `canFlowTo` ll && ll `canFlowTo` c =
--     let (Pair 0 p'@(Pg _ _ _ (TLabeledTCB a b))) = evalProgram p in
--         isPg p'
--     ==. True
--     *** QED
-- 
-- safeProgramEvalsToNonHole p@(Pg _ _ _ (TLabel _ _)) =
--     let (Pair 0 p'@(Pg _ _ _ _)) = evalProgram p in
--         isPg p'
--     ==. True
--     *** QED
-- 
-- safeProgramEvalsToNonHole p@(Pg _ _ _ (TUnlabel _)) = undefined
-- safeProgramEvalsToNonHole p@(Pg _ _ _ (TToLabeled _ _)) = undefined
-- safeProgramEvalsToNonHole p@(Pg _ _ _ t) = undefined

    


-- {-@ automatic-instances monotonicLabelEvalProgram @-}
{-@ monotonicLabelEvalProgram
 :: p:{Program | ς p && terminates p }
 -> {canFlowTo (pLabel p) (pLabel (pSnd (evalProgram p)))}
 / [evalSteps p, 0]
 @-}
monotonicLabelEvalProgram :: Program -> Proof
monotonicLabelEvalProgram p@(Pg l c m (TBind t1 t2)) = case evalProgram p of
    PgHole ->
        safeProgramEvalsToNonHole p
    (Pg l' c' m' t) ->
        let pInter = Pg l c m t1 in
            canFlowTo l l'
        ==. True ? safeProgramBindsToSafeProgram p t1 t2 &&& 
                   monotonicLabelEvalProgramStar pInter 
        *** QED

{- 
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
-}
monotonicLabelEvalProgram p@(Pg l c m t) = 
    let (Pg l' c' m' t) = evalProgram p in
        canFlowTo l l'
    ==. True
    *** QED

{-@ automatic-instances monotonicLabelEvalProgramStar @-}
{-@ monotonicLabelEvalProgramStar
 :: {p : Program | ς p && terminates p }
 -> {canFlowTo (pLabel p) (pLabel (pSnd (evalProgramStar p)))}
 / [evalSteps p, 1] 
 @-}
monotonicLabelEvalProgramStar :: Program -> Proof
monotonicLabelEvalProgramStar PgHole = unreachable
monotonicLabelEvalProgramStar p@(Pg l c m t) = case evalProgram p of
    PgHole ->
        safeProgramEvalsToNonHole p &&& unreachable

    p'@(Pg l' c' m' t') -> case evalProgramStar p' of
        PgHole ->
            unreachable
        (p''@(Pg l'' c'' m'' t'')) ->
          if ς p' then 
            terminationTheorem p                &&& 
            monotonicLabelEvalProgram p         &&& 
            monotonicLabelEvalProgramStar p' &&& 
            transitiveLabel l l' l''
            else admitted


{-@ measure terminates :: Program -> Bool @-}
{-@ measure evalSteps  :: Program -> Int  @-}

{-@ assume terminationTheorem :: {p:Program | terminates p} 
                       -> { 0 <= evalSteps p && 0 <= evalSteps (pSnd (evalProgram p)) &&  evalSteps (pSnd (evalProgram p)) < evalSteps p && terminates (pSnd (evalProgram p))} @-}
terminationTheorem :: Program -> Proof 
terminationTheorem _ = ()


{- stepsBind :: l:Label -> c:Label -> m:Memory
              -> t1:Term -> t2:Term
             -> {evalSteps (Pg l c m t1) < evalSteps (Pg l c m (TBind t1 t2))} @-}


-- monotonicLabelEvalProgramStar n p@(Pg l c m t) = case evalProgramStar (Pair n p) of
--     (Pair _ PgHole) ->
--         unreachable
--     (Pair _ (Pg l'' c'' m'' t'')) -> case evalProgram p of
--         (Pair _ PgHole) ->
--             safeProgramEvalsToNonHole p &&& unreachable
-- 
--         (Pair n' p'@(Pg l' c' m' t)) -> 
--             -- undefined
--             monotonicLabelEvalProgram p &&& monotonicLabelEvalProgramStar n' p' &&& transitiveLabel l l' l''


        -- monotonicLabelEvalProgram p

        --     canFlowTo l l''
        -- ==! canFlowTo l l'
        -- ==? True -- ? monotonicLabelEvalProgram p
        -- *** QED
        -- ==? canFlowTo l l'
        -- ==: True ? monotonicLabelEvalProgram p
        -- *** QED
        -- undefined

    -- where
    --     lToL' = 
    --         canFlowTo l l'
    --         ==. True ? monotonicLabelEvalProgram p
    --         *** QED


    --     canFlowTo l (pLabel (pSnd (evalProgramStar (Pair n p))))
    -- undefined
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

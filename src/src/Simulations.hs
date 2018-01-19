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

-- {-@ evalTHole :: {v : Proof | eval THole = THole} @-}
-- evalTHole :: Proof
-- evalTHole = undefined

simulations' :: Program -> Label -> Proof
{-@ simulations' 
  :: {p:Program | ς p && terminates p} 
  -> l:Label
  -> {v:Proof | evalEraseProgram (ε l p) l = ε l (evalProgram p)} @-}

simulations' (Pg lcurr c m t) l | not (lcurr `canFlowTo` l) -- l < lcurr
    = simulationsHoles' (Pg lcurr c m t) l

simulations' p l {- | lcurr <= l -}
  = simulations'' p l

-- simulations' (Pg lcurr c m t) l {- | lcurr <= l -}
--   =   evalEraseProgram (ε l (Pg lcurr c m t)) l 
--   ==! mapSnd (ε l) (evalProgram (ε l (Pg lcurr c m t)))
--   ==! mapSnd (ε l) (evalProgram (Pg lcurr c m (εTerm l t)))
--   ==! mapSnd (ε l) (Pair 0 (Pg lcurr c m (eval (εTerm l t))))
--   ==! Pair 0 (ε l (Pg lcurr c m (eval (εTerm l t))))
--   ==! Pair 1 (Pg lcurr c m (εTerm l (eval (εTerm l t))))
--   ==: Pair 0 (Pg lcurr c m (εTerm l (eval t))) ? eraseTermIdentity l t 
--   ==! Pair 0 (ε l (Pg lcurr c m (eval t)))
--   ==! mapSnd (ε l) (Pair 0 (Pg lcurr c m (eval t)))
--   ==! mapSnd (ε l) (evalProgram (Pg lcurr c m t))
--   *** QED 

{-@ simulations'' 
 :: {p : Program | ς p} 
 -> {l : Label | canFlowTo (pLabel p) l}
 -> {v : Proof | evalEraseProgram (ε l p) l = ε l (evalProgram p)}
 @-}
simulations'' :: Program -> Label -> Proof
-- simulations'' p@(Pg lc c m t@(TJoin t1 t2)) l = 
--     let (Pair εN εP) = evalProgram (Pg lc c m (TJoin (εTerm l t1) (εTerm l t2))) in
--         evalEraseProgram (ε l p) l
--     ==! mapSnd (ε l) (evalProgram (ε l p))
--     ==! mapSnd (ε l) (evalProgram (Pg lc c m (εTerm l t)))
--     ==! mapSnd (ε l) (evalProgram (Pg lc c m (TJoin (εTerm l t1) (εTerm l t2))))
--     ==? mapSnd (ε l) (evalProgram p)
--     *** QED

simulations'' p@(Pg lc c m t@(TLam v t1)) l = case propagateException t of
    True -> 
            evalEraseProgram (ε l p) l
        ==! ε l (evalProgram (ε l p))
        ==! ε l (evalProgram (Pg lc c m (εTerm l (TLam v t1))))
        -- ==! mapSnd (ε l) (evalProgram (Pg lc c m TException))
        ==! ε l (Pg lc c m (eval (εTerm l (TLam v t1))))
        ==: ε l (Pg lc c m TException) ? assertEqual (eval (TLam v t1)) TException &&& erasePropagateExceptionTrueEvalsToException l (TLam v t1)
        -- ==? mapSnd (ε l) (evalProgram p)
        -- ==! ε l (Pg lc c m TException)
        ==! ε l (Pg lc c m (eval (TLam v t1))) -- ? propagateExceptionFalseEvalsToNonexception t
        ==! ε l (evalProgram p)
        *** QED
        -- undefined
    False ->
            evalEraseProgram (ε l p) l
        ==! ε l (evalProgram (ε l p))
        ==! ε l (evalProgram (Pg lc c m (εTerm l (TLam v t1))))
        ==! ε l (evalProgram (Pg lc c m (TLam v (εTerm l t1))))
        ==! ε l (Pg lc c m (eval (TLam v (εTerm l t1))))
        ==: ε l (Pg lc c m (TLam v (εTerm l t1))) ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalseEvalsToNonexception l t
        ==! Pg lc c m (εTerm l (TLam v (εTerm l t1)))
        ==! Pg lc c m (TLam v (εTerm l (εTerm l t1)))
        ==: Pg lc c m (TLam v (εTerm l t1)) ? εTermIdempotent l t1
        ==! Pg lc c m (εTerm l (TLam v t1))
        ==! ε l (Pg lc c m (TLam v t1))
        ==: ε l (Pg lc c m (eval (TLam v t1))) ? propagateExceptionFalseEvalsToNonexception t
        ==! ε l (evalProgram p)
        *** QED

simulations'' p@(Pg lc c m t@(TApp t1 t2)) l = undefined
--         evalEraseProgram (ε l p) l
--         ==! mapSnd (ε l) (evalProgram (ε l p))
--         ==! mapSnd (ε l) (evalProgram (Pg lc c m (εTerm l t)))
--     ==! mapSnd (ε l) (evalProgram (ε l p))
--     ==! mapSnd (ε l) (evalProgram (Pg lc c m (εTerm l t)))
--     ==! mapSnd (ε l) (Pair 0 (Pg lc c m (eval (εTerm l t))))
--     ==! mapSnd (ε l) (Pair 0 (Pg lc c m (TApp (εTerm l t1) (εTerm l t2))))
--     ==! mapSnd (ε l) (evalProgram p)
--     *** QED

simulations'' p@(Pg lc c m t@TGetLabel) l = 
        evalEraseProgram (ε l p) l
    ==! ε l (evalProgram (Pg lc c m (εTerm l t)))
    ==! ε l (evalProgram (ε l (Pg lc c m t)))
    *** QED

simulations'' _ _ = undefined

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
            ==: PgHole ? simulationsHoles'' p l
            ==: ε l (Pg l' c' m' (TApp t2 t')) ? (safeProgramBindsToSafeProgram p t1 t2 &&& terminationAxiomTBind lc cc m t1 t2 &&& monotonicLabelEvalProgramStar p1 &&& greaterLabelNotFlowTo lc l' l)
            ==! ε l (Pg l' c' m' (TApp t2 t'))
            ==! ε l (evalProgram p)
            *** QED
        PgHole ->
                evalEraseProgram (ε l p) l
            ==: PgHole ? simulationsHoles'' p l
            ==! ε l PgHole
            ==! ε l (evalProgram p)
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
        ==: PgHole ? simulationsHoles'' p l
        ==! ε l ((Pg lc cc m' (TLabeledTCB ll t')))
        ==! ε l (evalProgram p)
        *** QED
        -- else

    (Pg l' _ m' t') ->
            evalEraseProgram (ε l p) l
        ==: PgHole ? simulationsHoles'' p l
        ==! ε l ((Pg lc cc m' (TLabeledTCB ll TException)))
        ==! ε l (evalProgram p)
        *** QED

    PgHole ->
        unreachable

simulationsHoles' p@(Pg lc cc m (TToLabeled (TVLabel _ll) _t)) l = 
        evalEraseProgram (ε l p) l
    ==: PgHole ? simulationsHoles'' p l
    ==! ε l (Pg lc cc m TException)
    ==! ε l (Pg lc cc m TException)
    ==! ε l (evalProgram p)
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

-- joinLeftNotFlowTo l lc ll = 
--         canFlowTo (join lc ll) l
--     ==. 
--     ==. False
--     *** QED

--        not (canFlowTo (join lc ll) l)
--    ==. not (canFlowTo lc l) ? joinLeftCanFlowTo lc ll l
--    ==. True

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

{- 
-- simulationsHoles' (Pg lcurr c m TException) l = 
--         evalEraseProgram (ε l (Pg lcurr c m TException)) l
--     ==. mapSnd (ε l) (evalProgram (ε l (Pg lcurr c m TException)))
-- 
--     ==. mapSnd (ε l) (evalProgram (Pg lcurr c m TException))
--     *** QED

simulationsHoles' (Pg lcurr c m TGetLabel) l = 
--         undefined
        evalEraseProgram (ε l (Pg lcurr c m TGetLabel)) l
    ==. mapSnd (ε l) (evalProgram (ε l (Pg lcurr c m TGetLabel)))
    ==. mapSnd (ε l) (evalProgram (Pg lcurr c m THole))
    ==. mapSnd (ε l) (Pair 0 (Pg lcurr c m (eval THole)))
    ==. mapSnd (ε l) (Pair 0 (Pg lcurr c m THole)) -- ? evalTHole
    ==. Pair 0 (ε l (Pg lcurr c m THole))
    ==. Pair 0 (Pg lcurr c m THole)
    ==. Pair 0 (ε l (Pg lcurr c m (TVLabel lcurr)))
    ==. mapSnd (ε l) (Pair 0 (Pg lcurr c m (TVLabel lcurr)))
    ==. mapSnd (ε l) (evalProgram (Pg lcurr c m TGetLabel))
    *** QED 

simulationsHoles' p@(Pg lcurr c m TGetClearance) l = 
--         undefined
        evalEraseProgram (ε l (Pg lcurr c m TGetClearance)) l
    ==. mapSnd (ε l) (evalProgram (ε l p))
    ==. mapSnd (ε l) (Pair 0 (Pg lcurr c m (eval THole)))
    ==. mapSnd (ε l) (Pair 0 (Pg lcurr c m THole))
    ==. Pair 0 (ε l (Pg lcurr c m THole))
    ==. Pair 0 (Pg lcurr c m THole)
    ==. Pair 0 (ε l (Pg lcurr c m (TVLabel c)))
    ==. mapSnd (ε l) (Pair 0 (Pg lcurr c m (TVLabel c)))
    ==. mapSnd (ε l) (evalProgram p)
    *** QED 

-- simulationsHoles' (Pg lcurr c m TGetLabel) l = undefined

simulationsHoles' (Pg lcurr c m t) l =
        evalEraseProgram (ε l (Pg lcurr c m t)) l
    ==. mapSnd (ε l) (evalProgram (ε l (Pg lcurr c m t)))
    ==. mapSnd (ε l) (evalProgram (Pg lcurr c m THole))
    ==. mapSnd (ε l) (Pair 0 (Pg lcurr c m (eval THole)))
    ==. mapSnd (ε l) (Pair 0 (Pg lcurr c m THole))
    ==. Pair 0 (ε l (Pg lcurr c m THole))
    ==. Pair 0 (Pg lcurr c m THole)
    ==. Pair 0 (ε l (Pg lcurr c m (eval t)))
    ==. mapSnd (ε l) (Pair 0 (Pg lcurr c m (eval t)))
    ==. mapSnd (ε l) (evalProgram (Pg lcurr c m t))
    *** QED 

-}

-- NV: the following holds just for now, when labels are added it will not hold
{- automatic-instances eraseTermIdentity @-}
{-@ eraseTermIdentity :: l:Label -> t:Term  -> { εTerm l t == t } / [size t] @-}
eraseTermIdentity :: Label -> Term -> Proof
eraseTermIdentity _ _ = undefined 
{- 
eraseTermIdentity _ THole          = trivial 
eraseTermIdentity _ TTrue          = trivial 
eraseTermIdentity _ TUnit          = trivial 
eraseTermIdentity _ TFalse         = trivial 
eraseTermIdentity _ (TVar _)       = trivial 
eraseTermIdentity l (TLam _ t)     = eraseTermIdentity l t
eraseTermIdentity l (TApp t1 t2)   = eraseTermIdentity l t1 &&& eraseTermIdentity l t2  
eraseTermIdentity l (TFix t)       = eraseTermIdentity l t 
eraseTermIdentity l (TIf t1 t2 t3) = eraseTermIdentity l t1 &&& eraseTermIdentity l t2 &&& eraseTermIdentity l t3 

eraseTermIdentity _ (TVLabel _)     = trivial
eraseTermIdentity l (TMeet t1 t2)      = eraseTermIdentity l t1 &&& eraseTermIdentity l t2
eraseTermIdentity l (TJoin t1 t2)      = eraseTermIdentity l t1 &&& eraseTermIdentity l t2
eraseTermIdentity l (TCanFlowTo t1 t2) = eraseTermIdentity l t1 &&& eraseTermIdentity l t2

eraseTermIdentity l (TBind t1 t2) = eraseTermIdentity l t1 &&& eraseTermIdentity l t2

eraseTermIdentity _ TGetLabel      = trivial
eraseTermIdentity _ TGetClearance  = trivial
eraseTermIdentity l (TLowerClearance t) = eraseTermIdentity l t

eraseTermIdentity l (TLabeledTCB _ t) = eraseTermIdentity l t
eraseTermIdentity l (TLabelOf t) = eraseTermIdentity l t
eraseTermIdentity l (TLabel t1 t2) = eraseTermIdentity l t1 &&& eraseTermIdentity l t2
eraseTermIdentity l (TUnlabel t) = eraseTermIdentity l t

eraseTermIdentity l (TToLabeled t1 t2) = eraseTermIdentity l t1 &&& eraseTermIdentity l t2

eraseTermIdentity _ TException  = trivial
-}

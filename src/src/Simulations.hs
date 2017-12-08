{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}

module Simulations where

import Label
import Language
import Programs 
import MetaFunctions 
import Simulations.Programs

import ProofCombinators

{-@ unsafeAssumeIndexEqual 
 :: n : Index 
 -> m : Index 
 -> {v : Proof | n == m}
 @-}
unsafeAssumeIndexEqual :: Index -> Index -> Proof
unsafeAssumeIndexEqual n m = undefined

{-@ simulationsCorollary 
  :: p:{Program | ς p} -> p':Program -> n:Index -> l:Label
  -> {v:Proof | evalProgram p == Pair n p'}
  -> (n'::Index, {v:Proof | n' <= n && evalEraseProgram (ε l p) l = Pair n' (ε l p')}) @-}
simulationsCorollary :: Program -> Program -> Index -> Label -> Proof -> (Index, Proof)
simulationsCorollary p p' n l evalProp = (n, simulations p p' n l evalProp)

simulations :: Program -> Program -> Index -> Label -> Proof -> Proof
{-@ simulations 
  :: {p:Program | ς p} -> p':Program -> n:Index -> l:Label
  -> {v:Proof | evalProgram p == Pair n p'}
  -> {v:Proof | evalEraseProgram (ε l p) l = Pair n (ε l p')} @-}
simulations p p' n l evalProp 
  =   evalEraseProgram (ε l p) l
  ==. mapSnd (ε l) (evalProgram p) ? simulations' p l
  ==. mapSnd (ε l) (Pair n p') ? evalProp
  ==. Pair n (ε l p')
  *** QED

-- {-@ evalTHole :: {v : Proof | eval THole = THole} @-}
-- evalTHole :: Proof
-- evalTHole = undefined

simulations' :: Program -> Label -> Proof
{-@ simulations' 
  :: {p:Program | ς p} -> l:Label
  -> {v:Proof | evalEraseProgram (ε l p) l = mapSnd (ε l) (evalProgram p)} @-}

simulations' (Pg lcurr c m t) l | not (lcurr `canFlowTo` l) -- l < lcurr
    = simulationsHoles' (Pg lcurr c m t) l

simulations' (Pg lcurr c m t) l {- | lcurr <= l -}
  =   evalEraseProgram (ε l (Pg lcurr c m t)) l 
  ==. mapSnd (ε l) (evalProgram (ε l (Pg lcurr c m t)))
  ==. mapSnd (ε l) (evalProgram (Pg lcurr c m (εTerm l t)))
  ==. mapSnd (ε l) (Pair 0 (Pg lcurr c m (eval (εTerm l t))))
  ==. Pair 0 (ε l (Pg lcurr c m (eval (εTerm l t))))
  ==. Pair 0 (Pg lcurr c m (εTerm l (eval (εTerm l t))))
  ==. Pair 0 (Pg lcurr c m (εTerm l (eval t))) ? eraseTermIdentity l t 
  ==. Pair 0 (ε l (Pg lcurr c m (eval t)))
  ==. mapSnd (ε l) (Pair 0 (Pg lcurr c m (eval t)))
  ==. mapSnd (ε l) (evalProgram (Pg lcurr c m t))
  *** QED 

simulations' PgHole _ | ς PgHole == False = unreachable

{-@ simulationsHoles'' :: p : {Program | ς p} -> {l : Label | not (canFlowTo (pLabel p) l)} -> {v:Proof | evalEraseProgram (ε l p) l = Pair 0 PgHole} @-}
simulationsHoles'' :: Program -> Label -> Proof
simulationsHoles'' p@(Pg _ _ _ _) l =
        evalEraseProgram (ε l p) l
    ==. evalEraseProgram PgHole l
    ==. mapSnd (ε l) (evalProgram PgHole)
    ==. mapSnd (ε l) (Pair 0 PgHole)
    ==. Pair 0 (ε l PgHole)
    ==. Pair 0 PgHole
    *** QED

simulationsHoles'' PgHole _ | ς PgHole == False = unreachable

{-@ monotonicLabelEvalProgramStar
 :: n : Index
 -> n' : Index
 -> p : Program
 -> {p' : Program | evalProgramStar (Pair n p) == (Pair n' p')}
 -> {v : Proof | canFlowTo (pLabel p) (pLabel p')}
 @-}
monotonicLabelEvalProgramStar :: Index -> Index -> Program -> Program -> Proof
monotonicLabelEvalProgramStar n n' p p' =
    undefined
    -- TODO: Unimplemented XXX

-- Simulations case when there are holes (current label exceeds output label).
{-@ simulationsHoles' 
  :: {p : Program | ς p}
  -> {l : Label | not (canFlowTo (pLabel p) l)}
  -> {v:Proof | evalEraseProgram (ε l p) l = mapSnd (ε l) (evalProgram p)} @-}

simulationsHoles' :: Program -> Label -> Proof
simulationsHoles' p@(Pg lc cc m (TBind t1 t2)) l = 
    let p1 = Pg lc cc m t1 in
    case evalProgramStar (Pair 0 p1) of
        (Pair n ps@(Pg l' c' m' t')) -> 
                evalEraseProgram (ε l p) l
            ==: Pair 0 PgHole ? simulationsHoles'' p l
            ==: Pair n PgHole ? unsafeAssumeIndexEqual 0 n
            ==: Pair n (ε l (Pg l' c' m' (TApp t2 t'))) ? (monotonicLabelEvalProgramStar 0 n p1 ps &&& greaterLabelNotFlowTo lc l' l)
            ==! mapSnd (ε l) (Pair n (Pg l' c' m' (TApp t2 t')))
            ==! mapSnd (ε l) (evalProgram p)
            *** QED
        (Pair n PgHole) ->
                evalEraseProgram (ε l p) l
            ==: Pair 0 PgHole ? simulationsHoles'' p l
            ==: Pair n PgHole ? unsafeAssumeIndexEqual 0 n
            ==! Pair n (ε l PgHole)
            ==! mapSnd (ε l) (Pair n PgHole)
            ==! mapSnd (ε l) (evalProgram p)
            *** QED

simulationsHoles' p@(Pg lc cc m TGetLabel) l =
        evalEraseProgram (ε l p) l
    ==. Pair 0 PgHole ? simulationsHoles'' p l
    ==. Pair 0 (ε l (Pg lc cc m (TVLabel lc)))
    ==. mapSnd (ε l) (Pair 0 (Pg lc cc m (TVLabel lc)))
    ==. mapSnd (ε l) (evalProgram p)
    *** QED

simulationsHoles' p@(Pg lc cc m TGetClearance) l =
        evalEraseProgram (ε l p) l
    ==. Pair 0 PgHole ? simulationsHoles'' p l
    ==. Pair 0 (ε l (Pg lc cc m (TVLabel cc)))
    ==. mapSnd (ε l) (Pair 0 (Pg lc cc m (TVLabel cc)))
    ==. mapSnd (ε l) (evalProgram p)
    *** QED

simulationsHoles' p@(Pg lc cc m (TLowerClearance (TVLabel c'))) l | lc `canFlowTo` c' && c' `canFlowTo` cc = 
        evalEraseProgram (ε l p) l
    ==. Pair 0 PgHole ? simulationsHoles'' p l
    ==. Pair 0 (ε l (Pg lc c' m TUnit))
    ==. mapSnd (ε l) (Pair 0 (Pg lc c' m TUnit))
    ==. mapSnd (ε l) (evalProgram p)
    *** QED

simulationsHoles' p@(Pg lc cc m (TLowerClearance (TVLabel _c'))) l = 
        evalEraseProgram (ε l p) l
    ==. Pair 0 PgHole ? simulationsHoles'' p l
    ==. Pair 0 (ε l (Pg lc cc m TException))
    ==. mapSnd (ε l) (Pair 0 (Pg lc cc m TException))
    ==. mapSnd (ε l) (evalProgram p)
    *** QED

simulationsHoles' p@(Pg lc cc m (TLabel (TVLabel ll) t)) l | lc `canFlowTo` ll && ll `canFlowTo` cc =
        evalEraseProgram (ε l p) l
    ==. Pair 0 PgHole ? simulationsHoles'' p l
    ==. Pair 0 (ε l (Pg lc cc m (TLabeledTCB ll t)))
    ==. mapSnd (ε l) (Pair 0 (Pg lc cc m (TLabeledTCB ll t)))
    ==. mapSnd (ε l) (evalProgram p)
    *** QED

simulationsHoles' p@(Pg lc cc m (TLabel (TVLabel _ll) _)) l 
    =   evalEraseProgram (ε l p) l
    ==. Pair 0 PgHole ? simulationsHoles'' p l
    ==. Pair 0 (ε l (Pg lc cc m TException))
    ==. mapSnd (ε l) (Pair 0 (Pg lc cc m TException))
    ==. mapSnd (ε l) (evalProgram p)
    *** QED

simulationsHoles' p@(Pg lc cc m (TUnlabel (TLabeledTCB ll t))) l | (lc `join` ll) `canFlowTo` cc = 
        evalEraseProgram (ε l p) l
    ==. Pair 0 PgHole ? simulationsHoles'' p l
    ==. Pair 0 (ε l (Pg (lc `join` ll) cc m t)) ? joinLeftNotFlowTo l lc ll
    ==. mapSnd (ε l) (Pair 0 (Pg (lc `join` ll) cc m t))
    ==. mapSnd (ε l) (evalProgram p)
    *** QED

simulationsHoles' p@(Pg lc cc m (TUnlabel (TLabeledTCB ll t))) l =
        evalEraseProgram (ε l p) l
    ==. Pair 0 PgHole ? simulationsHoles'' p l
    ==. Pair 0 (ε l (Pg lc cc m TException))
    ==. mapSnd (ε l) (Pair 0 (Pg lc cc m TException))
    ==. mapSnd (ε l) (evalProgram p)
    *** QED

simulationsHoles' p@(Pg lc cc m (TToLabeled (TVLabel ll) t)) l | lc `canFlowTo` ll && ll `canFlowTo` cc = 
    undefined
    --     evalEraseProgram (ε l p) l
    -- ==: Pair 0 PgHole ? simulationsHoles'' p l
    -- ==! mapSnd (ε l) (evalProgram p)
    -- *** QED

simulationsHoles' p@(Pg lc cc m (TToLabeled (TVLabel _ll) _t)) l = 
        evalEraseProgram (ε l p) l
    ==: Pair 0 PgHole ? simulationsHoles'' p l
    ==! Pair 0 (ε l (Pg lc cc m TException))
    ==! mapSnd (ε l) (Pair 0 (Pg lc cc m TException))
    ==! mapSnd (ε l) (evalProgram p)
    *** QED

simulationsHoles' p@(Pg lc cc m t) l = 
    let t' = eval t in
        evalEraseProgram (ε l p) l
    ==. Pair 0 PgHole ? simulationsHoles'' p l
    ==. Pair 0 (ε l (Pg lc cc m t'))
    ==. mapSnd (ε l) (Pair 0 (Pg lc cc m t'))
    ==. mapSnd (ε l) (Pair 0 (Pg lc cc m (eval t)))
    ==. mapSnd (ε l) (evalProgram p)
    *** QED

simulationsHoles' PgHole l =
        evalEraseProgram (ε l PgHole) l
    ==. Pair 0 PgHole ? simulationsHoles'' PgHole l
    ==. mapSnd (ε l) (evalProgram PgHole)
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

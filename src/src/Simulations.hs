{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}

module Simulations where

import Language.Haskell.Liquid.ProofCombinators

import Language 
import Programs 
import MetaFunctions 

{-@ simulationsCorollary 
  :: p:Program -> p':Program -> n:Index -> l:Label
  -> {v:Proof | evalProgram p == Pair n p'}
  -> (n'::Index, {v:Proof | n' <= n && evalEraseProgram (ε l p) l = Pair n' (ε l p')}) @-}
simulationsCorollary :: Program -> Program -> Index -> Label -> Proof -> (Index, Proof)
simulationsCorollary p p' n l evalProp = (n, simulations p p' n l evalProp)

simulations :: Program -> Program -> Index -> Label -> Proof -> Proof
{-@ simulations 
  :: p:Program -> p':Program -> n:Index -> l:Label
  -> {v:Proof | evalProgram p == Pair n p'}
  -> {v:Proof | evalEraseProgram (ε l p) l = Pair n (ε l p')} @-}
simulations p p' n l evalProp 
  =   evalEraseProgram (ε l p) l 
  ==. mapSnd (ε l) (evalProgram p) ? simulations' p l 
  ==. mapSnd (ε l) (Pair n p')     ? evalProp
  ==. Pair n (ε l p')
  *** QED 

{-@ evalTHole :: {v : Proof | eval THole = THole} @-}
evalTHole :: Proof
evalTHole = undefined

simulations' :: Program -> Label -> Proof
{-@ simulations' 
  :: p:Program -> l:Label
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

-- Simulations case when there are holes (current label exceeds output label).
{-@ simulationsHoles' 
  :: p : Program 
  -> {l : Label | not (canFlowTo (pLabel p) l)}
  -> {v:Proof | evalEraseProgram (ε l p) l = mapSnd (ε l) (evalProgram p)} @-}

simulationsHoles' :: Program -> Label -> Proof
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
    ==. Pair 0 (ε l (Pg lcurr c m (TLabel lcurr)))
    ==. mapSnd (ε l) (Pair 0 (Pg lcurr c m (TLabel lcurr)))
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
    ==. Pair 0 (ε l (Pg lcurr c m (TLabel c)))
    ==. mapSnd (ε l) (Pair 0 (Pg lcurr c m (TLabel c)))
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

-- NV: the following holds just for now, when labels are added it will not hold
{-@ automatic-instances eraseTermIdentity @-}
{-@ eraseTermIdentity :: l:Label -> t:Term  -> { εTerm l t == t } / [size t] @-}
eraseTermIdentity :: Label -> Term -> Proof
eraseTermIdentity _ THole          = trivial 
eraseTermIdentity _ TTrue          = trivial 
eraseTermIdentity _ TUnit          = trivial 
eraseTermIdentity _ TFalse         = trivial 
eraseTermIdentity _ (TVar _)       = trivial 
eraseTermIdentity l (TLam _ t)     = eraseTermIdentity l t
eraseTermIdentity l (TApp t1 t2)   = eraseTermIdentity l t1 &&& eraseTermIdentity l t2  
eraseTermIdentity l (TFix t)       = eraseTermIdentity l t 
eraseTermIdentity l (TIf t1 t2 t3) = eraseTermIdentity l t1 &&& eraseTermIdentity l t2 &&& eraseTermIdentity l t3 

eraseTermIdentity _ (TLabel _)     = trivial
eraseTermIdentity l (TMeet t1 t2)      = eraseTermIdentity l t1 &&& eraseTermIdentity l t2
eraseTermIdentity l (TJoin t1 t2)      = eraseTermIdentity l t1 &&& eraseTermIdentity l t2
eraseTermIdentity l (TCanFlowTo t1 t2) = eraseTermIdentity l t1 &&& eraseTermIdentity l t2

eraseTermIdentity l (TBind t1 t2) = eraseTermIdentity l t1 &&& eraseTermIdentity l t2

eraseTermIdentity _ TGetLabel      = trivial
eraseTermIdentity _ TGetClearance  = trivial
-- eraseTermIdentity l (TLowerClearance t) = eraseTermIdentity l t

eraseTermIdentity _ TException  = trivial

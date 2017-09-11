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

simulations' :: Program -> Label -> Proof
{-@ simulations' 
  :: p:Program -> l:Label
  -> {v:Proof | evalEraseProgram (ε l p) l = mapSnd (ε l) (evalProgram p)} @-}
simulations' (Pg lcurr m t) l | l < lcurr
  =   evalEraseProgram (ε l (Pg lcurr m t)) l
  ==. mapSnd (ε l) (evalProgram (ε l (Pg lcurr m t)))
  ==. mapSnd (ε l) (evalProgram (Pg lcurr m THole))
  ==. mapSnd (ε l) (Pair 0 (Pg lcurr m (eval THole)))
  ==. mapSnd (ε l) (Pair 0 (Pg lcurr m THole))
  ==. Pair 0 (ε l (Pg lcurr m THole))
  ==. Pair 0 (Pg lcurr m THole)
  ==. Pair 0 (ε l (Pg lcurr m (eval t)))
  ==. mapSnd (ε l) (Pair 0 (Pg lcurr m (eval t)))
  ==. mapSnd (ε l) (evalProgram (Pg lcurr m t))
  *** QED 

simulations' (Pg lcurr m t) l {- | lcurr <= l -}
  =   evalEraseProgram (ε l (Pg lcurr m t)) l 
  ==. mapSnd (ε l) (evalProgram (ε l (Pg lcurr m t)))
  ==. mapSnd (ε l) (evalProgram (Pg lcurr m (εTerm l t)))
  ==. mapSnd (ε l) (Pair 0 (Pg lcurr m (eval (εTerm l t))))
  ==. Pair 0 (ε l (Pg lcurr m (eval (εTerm l t))))
  ==. Pair 0 (Pg lcurr m (εTerm l (eval (εTerm l t))))
  ==. Pair 0 (Pg lcurr m (εTerm l (eval t))) ? eraseTermIdentity l t 
  ==. Pair 0 (ε l (Pg lcurr m (eval t)))
  ==. mapSnd (ε l) (Pair 0 (Pg lcurr m (eval t)))
  ==. mapSnd (ε l) (evalProgram (Pg lcurr m t))
  *** QED 

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
eraseTermIdentity l (TIF t1 t2 t3) = eraseTermIdentity l t1 &&& eraseTermIdentity l t2 &&& eraseTermIdentity l t3 


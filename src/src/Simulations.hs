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

simulations' (Pg lcurr c m t) l | not (lcurr `canFlowTo` l) -- l < lcurr
  =   evalEraseProgram (ε l (Pg lcurr c m t)) l
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

-- simulations' p@(Pg lc c m TGetLabel) l {- | lcurr <= l -}
--   = evalEraseProgram (ε l p)
--   ==. mapSnd (ε l) (evalProgram (ε l p))
--   ==. mapSnd (ε l) (Pair 0 (Pg lc c m (eval (TLabel lc))))
--   ==. mapSnd (ε l) (Pair 0 (Pg lc c m (TLabel lc)))
--   ==. Pair 0 (ε l (Pg lc c m (TLabel lc)))
--   ==. Pair 0 (Pg lc c m (TLabel lc))
--   ==. Pair 0 (ε l (Pg lc c m (eval TGetLabel)))
--   ==. mapSnd (ε l) (Pair 0 (Pg lc c m (eval TGetLabel)))
--   ==. mapSnd (ε l) (evalProgram (Pg lc c m TGetLabel))
--   *** QED

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
eraseTermIdentity l (TIF t1 t2 t3) = eraseTermIdentity l t1 &&& eraseTermIdentity l t2 &&& eraseTermIdentity l t3 

eraseTermIdentity _ (TLabel _)     = trivial

eraseTermIdentity _ TGetLabel      = trivial
eraseTermIdentity _ TGetClearance  = trivial

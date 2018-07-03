-- | Axiomatization of Termination

{-@ measure terminates :: Program l -> Bool @-}


-- | Eval steps is used as a termination metric to prove eval terminates

{-@ measure evalSteps :: Program l -> Int @-}


-- | Assumed invariant: all programs terminate
-- | to prove this we need to 1. propagate the assumed termination properties 
-- | to all the functions, e.g., erasure and 2. assume that for each term
-- | if a term terminates each of its subterms terminate 

{-@ invariant { p:Program l | terminates p }  @-}

{-@ assume evalStepsAxiomErase :: Label l => l:l -> p:{Program l | terminates p } -> 
  {  terminates (eval (ε l p))
  && (evalSteps (eval (ε l p)) < evalSteps p)
  && (0 <= evalSteps (eval (ε l p)))
  && (0 <= evalSteps p) } @-}
evalStepsAxiomErase :: Label l => l -> Program l -> Proof 
evalStepsAxiomErase _ _ = () 

{-@ assume evalStepsAxiom :: p:{Program l | terminates p } -> 
  {  (evalSteps (eval p) < evalSteps p) 
  && (0 <= evalSteps (eval p))
  && (0 <= evalSteps p)
  && terminates (eval p) 
  && terminates (evalStar p) } @-}
evalStepsAxiom :: Program l -> Proof 
evalStepsAxiom _ = () 

{-@ assume evalStepsNatAxiom :: p:Program l -> { 0 <= evalSteps p } @-}
evalStepsNatAxiom :: Program l -> Proof 
evalStepsNatAxiom _ = () 

{-@ assume evalStepsToLabeledAxiom 
  :: lc:l 
  -> db:DB l 
  -> t1:Term l 
  -> t2:{Term l | terminates (Pg lc db (TToLabeled t1 t2)) } 
  -> { evalSteps (Pg lc db t2) < evalSteps (Pg lc db (TToLabeled t1 t2)) 
    && 0 <= evalSteps (Pg lc db t2)
    && terminates (Pg lc db t2)    } @-}
evalStepsToLabeledAxiom :: l -> DB l -> Term l -> Term l -> Proof 
evalStepsToLabeledAxiom _ _ _ _ = () 

{-@ assume evalStepsBindAxiom :: lc:l -> db:DB l -> t1:Term l 
   -> t2:{Term l | terminates (Pg lc db (TBind t1 t2)) } -> 
  {  (evalSteps (Pg lc db t1) < evalSteps (Pg lc db (TBind t1 t2))) 
  && (0 <= evalSteps (Pg lc db t1))
  && (terminates (Pg lc db t1))} @-}
evalStepsBindAxiom :: l -> DB l -> Term l -> Term l -> Proof 
evalStepsBindAxiom _ _ _ _ = () 

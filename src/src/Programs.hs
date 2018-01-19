{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}
{-@ LIQUID "--trustinternals"                           @-}

{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
module Programs where

import Label
import Language 

-- LH bug: why this is not given?
{-@ assume pLabel :: p:Program -> {l:Label | pLabel p == l} @-}

data Program =
      Pg {pLabel :: Label, pClearance :: Label, pMemory :: Memory, pTerm :: Term}
    | PgHole
  deriving (Eq, Show)

{-@ data Program <p :: Term -> Bool>
  = Pg { pLabel     :: Label
       , pClearance :: Label
       , pMemory    :: Memory
       , pTerm      :: (Term<p>)
       }
    | PgHole
 @-}

data Memory  = Memory deriving (Eq, Show)
{-@ reflect evalProgram @-}
evalProgram :: Program -> Program
evalProgram PgHole =  PgHole

evalProgram (Pg l c m (TBind t1 t2)) = 
    case evalProgramStar (Pg l c m t1) of
        (Pg l' c' m' t') -> Pg l' c' m' (TApp t2 t')

evalProgram (Pg l c m TGetLabel)     = Pg l c m (TVLabel l)
evalProgram (Pg l c m TGetClearance) = Pg l c m (TVLabel c)

-- Lower clearance where checks pass.
evalProgram (Pg l c m (TLowerClearance (TVLabel c'))) | l `canFlowTo` c' && c' `canFlowTo` c = 
    Pg l c' m TUnit
    
-- Lower clearance where checks don't pass.
evalProgram (Pg l c m (TLowerClearance (TVLabel _))) 
  = Pg l c m TException

-- Label where checks pass.
evalProgram (Pg l c m (TLabel (TVLabel ll) t)) | l `canFlowTo` ll && ll `canFlowTo` c 
  = Pg l c m (TLabeledTCB ll t)

-- Label where checks don't pass.
-- evalProgram (Pg l c m (TLabel (TVLabel ll) _)) | not (l `canFlowTo` ll && ll `canFlowTo` c) = Pair 0 (Pg l c m TException)
evalProgram (Pg l c m (TLabel (TVLabel _) _)) 
  = Pg l c m TException

-- Unlabel.
evalProgram (Pg lc cc m (TUnlabel (TLabeledTCB ll t))) = 
    let l' = lc `join` ll in
    -- Checks pass.
    if l' `canFlowTo` cc then
        Pg l' cc m t
    -- Checks don't pass.
    else
        Pg lc cc m TException -- JP: Not l' right?

-- ToLabeled.
evalProgram (Pg l c m (TToLabeled (TVLabel ll) t)) | l `canFlowTo` ll && ll `canFlowTo` c = 
    case evalProgramStar (Pg l c m t) of
        (Pg l' _ m' t') -> 
            if l' `canFlowTo` ll then
                Pg l c m' (TLabeledTCB ll t')
            else
                Pg l c m' (TLabeledTCB ll TException)

        -- JP: Does this make sense? What do we do for labels + memory?
        -- (Pair n PgHole) ->  
        --       Pair (n+1) (Pg l c m (TLabeledTCB ll THole))
            
evalProgram (Pg l c m (TToLabeled (TVLabel _) _)) = Pg l c m TException

evalProgram (Pg l c m t) = Pg l c m (eval t)


-- JP: Can we drop evalProgramStar and evaluate with small steps?

{-@ lazy evalProgramStar @-}

{-@ reflect evalProgramStar @-}
-- TODO: 
-- {-@ evalProgramStar :: Pair Index Program -> Pair Index (Program <{\v -> isValue v}>) @-}
{-@ evalProgramStar 
 :: Program 
 -> {p' : Program | isPg p' && isValue (pTerm p')} 
@-}
evalProgramStar :: Program -> Program
evalProgramStar (Pg l c m t) | isValue t 
  = Pg l c m t
evalProgramStar p 
  = evalProgramStar (evalProgram p)


-- JP: TODO What about THOLE??? XXX
{-@ measure isPg @-}
isPg :: Program -> Bool
isPg PgHole = False
isPg _ = True
-- isPg p = not (isHole p)
-- isPg = not . isHole
-- {-@ measure isHole @-}
-- isHole :: Program -> Bool
-- isHole PgHole = True

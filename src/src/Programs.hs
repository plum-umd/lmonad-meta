{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}
{-@ LIQUID "--trustinternals"                           @-}

{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
module Programs where

import Label
import Language 

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

data Memory  = Memory
  deriving (Eq, Show)
type Index = Integer

data Pair a b = Pair {pFst :: a, pSnd :: b}
  deriving Eq 
{-@ data Pair a b = Pair {pFst :: a, pSnd :: b} @-}

{-@ reflect evalProgram @-}
evalProgram :: Program -> Pair Index Program
evalProgram PgHole = Pair 0 PgHole

evalProgram (Pg l c m (TBind t1 t2)) = 
    case evalProgramStar (Pair 0 (Pg l c m t1)) of
        (Pair n (Pg l' c' m' t')) -> 
            Pair n (Pg l' c' m' (TApp t2 t'))
        (Pair n PgHole) ->
            Pair n PgHole

evalProgram (Pg l c m TGetLabel) = Pair 0 (Pg l c m (TVLabel l))
evalProgram (Pg l c m TGetClearance) = Pair 0 (Pg l c m (TVLabel c))

-- Lower clearance where checks pass.
evalProgram (Pg l c m (TLowerClearance (TVLabel c'))) | l `canFlowTo` c' && c' `canFlowTo` c = 
    Pair 0 (Pg l c' m TUnit)
    
-- Lower clearance where checks don't pass.
evalProgram (Pg l c m (TLowerClearance (TVLabel _))) = Pair 0 (Pg l c m TException)

-- Label where checks pass.
evalProgram (Pg l c m (TLabel (TVLabel ll) t)) | l `canFlowTo` ll && ll `canFlowTo` c = Pair 0 (Pg l c m (TLabeledTCB ll t))

-- Label where checks don't pass.
evalProgram (Pg l c m (TLabel (TVLabel _) _)) = Pair 0 (Pg l c m TException)

-- Unlabel.
evalProgram (Pg l c m (TUnlabel (TLabeledTCB ll t))) = 
    let l' = l `join` ll in
    -- Checks pass.
    if l' `canFlowTo` c then
        Pair 0 (Pg l' c m t)
    -- Checks don't pass.
    else
        Pair 0 (Pg l c m TException) -- JP: Not l' right?

-- ToLabeled.
evalProgram (Pg l c m (TToLabeled (TVLabel ll) t)) | l `canFlowTo` ll && ll `canFlowTo` c = 
    case evalProgramStar (Pair 0 (Pg l c m t)) of
        (Pair n (Pg l' _ m' t')) -> 
            if l' `canFlowTo` ll then
                Pair (n+1) (Pg l c m' (TLabeledTCB ll t'))
            else
                Pair (n+1) (Pg l c m' (TLabeledTCB ll TException))

        -- JP: Does this make sense? What do we do for labels + memory?
        (Pair n PgHole) ->
            Pair (n+1) (Pg l c m (TLabeledTCB ll THole))
            
evalProgram (Pg l c m (TToLabeled (TVLabel _) _)) = Pair 0 (Pg l c m TException)

evalProgram (Pg l c m t) = Pair 0 (Pg l c m (eval t))

{-@ lazy evalProgramStar @-}

{-@ reflect evalProgramStar @-}
{-@ evalProgramStar :: Pair Index Program -> Pair Index (Program <{\v -> isValue v}>) @-}
evalProgramStar :: Pair Index Program -> Pair Index Program
evalProgramStar (Pair n (Pg l c m t))
  | isValue t 
  = Pair n (Pg l c m t)
evalProgramStar (Pair n p) =
    let (Pair n' p') = evalProgramStar (evalProgram p) in
    Pair (n + n') p'


{-@ reflect mapSnd @-}
mapSnd :: (b -> c) -> Pair a b -> Pair a c 
mapSnd f (Pair x y) = Pair x (f y)

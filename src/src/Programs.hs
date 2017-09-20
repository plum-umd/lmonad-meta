data Program = Pg {pLabel :: Label, pClearance :: Label, pMemory :: Memory, pTerm :: Term}
  deriving (Eq, Show)
data Memory  = Memory
  deriving (Eq, Show)
type Index = Integer

{-@ data Program = Pg {pLabel :: Label, pClearance :: Label, pMemory :: Memory, pTerm :: Term} @-}
{-@ data Memory  = Memory @-}

data Pair a b = Pair {pFst :: a, pSnd :: b}
  deriving Eq 
{-@ data Pair a b = Pair {pFst :: a, pSnd :: b} @-}

{-@ reflect evalProgram @-}
evalProgram :: Program -> Pair Index Program
evalProgram (Pg l c m TGetLabel) = Pair 0 (Pg l c m (TLabel l))
evalProgram (Pg l c m TGetClearance) = Pair 0 (Pg l c m (TLabel c))

-- -- Lower clearance where checks pass.
-- evalProgram (Pg l c m (TLowerClearance (TLabel c'))) | l `canFlowTo` c' && c' `canFlowTo` c = 
--     Pair 0 (Pg l c' m TUnit)
--     
-- -- TODO: Lower clearance where checks pass. XXX
-- evalProgram (Pg l c m (TLowerClearance (TLabel c'))) | l `canFlowTo` c' && c' `canFlowTo` c = undefined
-- 
-- evalProgram (Pg l c m (TLowerClearance t)) = evalProgram (Pg l c m (TLowerClearance (eval t)))

evalProgram (Pg l c m t) = Pair 0 (Pg l c m (eval t))

{-@ reflect evalEraseProgram @-}
evalEraseProgram :: Program -> Label -> Pair Index Program 
evalEraseProgram p l = mapSnd (ε l) (evalProgram p)

{-@ reflect mapSnd @-}
mapSnd :: (b -> c) -> Pair a b -> Pair a c 
mapSnd f (Pair x y) = Pair x (f y)

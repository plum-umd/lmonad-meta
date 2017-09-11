data Program = Pg {pLabel :: Label, pMemory :: Memory, pTerm :: Term}
  deriving Eq 
data Memory  = Memory
  deriving Eq
type Index = Integer

{-@ data Program = Pg {pLabel :: Label, pMemory :: Memory, pTerm :: Term} @-}
{-@ data Memory  = Memory @-}

data Pair a b = Pair {pFst :: a, pSnd :: b}
  deriving Eq 
{-@ data Pair a b = Pair {pFst :: a, pSnd :: b} @-}

-- | NV QUESTION: is index input or output?

{-@ reflect evalProgram @-}
evalProgram :: Program -> Pair Index Program
evalProgram (Pg l m t) = Pair 0 (Pg l m (eval t))

{-@ reflect evalEraseProgram @-}
evalEraseProgram :: Program -> Label -> Pair Index Program 
evalEraseProgram p l = mapSnd (ε l) (evalProgram p)

{-@ reflect mapSnd @-}
mapSnd :: (b -> c) -> Pair a b -> Pair a c 
mapSnd f (Pair x y) = Pair x (f y)
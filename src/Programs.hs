{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}
{-@ LIQUID "--trustinternals"                           @-}

{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
module Programs where

import Data.Map.Strict (Map)
import Label
import Language 
import ProofCombinators

-- LH bug: why this is not given?
{-@ assume pLabel :: p:Program -> {l:Label | pLabel p == l} @-}

data Program =
      Pg {pLabel :: Label, pClearance :: Label, pDatabase :: Database, pTerm :: Term}
    | PgHole
  deriving (Eq, Show)

-- instance Show Program where
--     show = showHelper 0
--         where
--             showTerm _ THole = "•"
--             showTerm _ TTrue = "True"
--             showTerm _ TFalse = "False"
--             showTerm _ TUnit = "()"
--             showTerm _ (TVar i) = "v" ++ show i
--             showTerm i (TApp t1 t2) = "(" ++ showTerm 0 t1 ++ ") (" ++ showTerm 0 t2 ++ ")"
-- 
--             showTerm i (TBind t1 (TLam v t2)) = showTerm 0 (TVar v) ++ " <- " ++ show t1 ++ "\n" ++ showTerm i t2
--             showTerm _ t@(TBind t1 t2) = show t
-- 
--             showTerm _ t = show t
-- 
--             showHelper i p = do
--                    indents i
--                 ++ showTerm i (pTerm p)
--                 -- TODO: Show DB, label/clearance
-- 
--             indents i = replicate i ' '

{-@ data Program <p :: Term -> Bool>
  = Pg { pLabel     :: Label
       , pClearance :: Label
       , pMemory    :: Memory
       , pTerm      :: (Term<p>)
       }
    | PgHole
 @-}

-- newtype Map k v = Map [(k,v)]
--     deriving (Show)

data DBValue = DBValue Term
    -- | Option types, bools, unit, 
    deriving (Eq, Show)

data DBLabelFunction = DBLabelFunction Term
    -- | Function that takes columns from a row and returns that column's label.
    deriving (Eq, Show)

type ColumnName = Int
data Table = Table {
      tableRows :: [Map ColumnName DBValue]
    , tableLabelFunctions :: Map ColumnName DBLabelFunction
    }
    deriving (Eq, Show)

type TableName = Int
data Database = Database (Map TableName Table) 
    deriving (Eq, Show)

{-@ reflect evalProgram @-}
{-@ evalProgram
 :: p : Program
 -> p' : {Program | isPg p => isPg p'}
 @-}
evalProgram :: Program -> Program
-- JP: Should we check to propagate exceptions here?
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
 :: p : Program 
 -> {p' : Program | (isPg p => isPg p' && isValue (pTerm p'))} 
@-}
evalProgramStar :: Program -> Program
evalProgramStar PgHole = PgHole
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

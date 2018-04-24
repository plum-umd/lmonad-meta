{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}
{-@ LIQUID "--trustinternals"                           @-}

{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
module Programs where

import Data.Map (Map)
import qualified Data.Map as Map
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
       , pDatabase  :: Database
       , pTerm      :: (Term<p>)
       }
    | PgHole
 @-}

-- newtype Map k v = Map [(k,v)]
--     deriving (Show)

data DBValue = DBValue Term
    -- | Option types, bools, unit, ints
    deriving (Eq, Show)

newtype DBLabelFunction = DBLabelFunction (PrimaryKey -> Row -> Label) -- Term
    -- | Function that takes columns from a row and returns that column's label.
    -- deriving (Eq, Show)

newtype Row = Row (Map ColumnName DBValue)
    deriving (Eq, Show)

data Table = Table {
      tableRows :: Map PrimaryKey Row
    , tableLabelFunctions :: Map ColumnName DBLabelFunction
    , tableLabel :: Label
    }

instance Eq Table where
    (Table a _ l) == (Table b _ l') = a == b && l == l'

instance Show Table where
    show (Table t _ _) = "Table " ++ show t

-- data Database = Database (Map TableName Table) 
--     deriving (Eq, Show)
type Database = Map TableName Table

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

evalProgram (Pg l c m (TPInsert n rs)) | Just rs' <- evalPRow rs = 
    Pg l c m (TInsert n rs')

evalProgram (Pg l c m (TPInsert n rs)) | Map.lookup n m == Nothing =
    Pg l c m TException

evalProgram (Pg l c m (TPInsert n rs)) | Just Table{..} <- Map.lookup n m =
    -- Get fresh key.
    let k = freshKey tableRows in

    -- Convert row.
    let (ls', rs') = convertRow rs in
    let rs'' = Row (Map.fromList rs') in
    let ls'' = Map.fromList ls' in

    -- Check label for each field.
    let tableCheck = l `canFlowTo` tableLabel && tableLabel `canFlowTo` c in
    let checks = Map.foldlWithKey (checkLabel k ls'' rs'') tableCheck tableLabelFunctions in
    -- JP: What about the check for the old clearance used to create the Labeled? I guess this doesn't impact NI
    if checks then
        -- Insert row.
        let tableRows' = Map.insert k rs'' tableRows in

        -- Update table.
        let m' = Map.insert n (Table tableRows' tableLabelFunctions tableLabel) m in

        Pg l c m' TUnit

    else
        Pg l c m TException

    where
        checkLabel _ _ _ False _ _ = False
        checkLabel k ls rs True k' (DBLabelFunction labelF) = 
            case Map.lookup k' ls of
                Nothing ->
                    -- Label not found, so return exception. This is impossible w/ Haskell's type system.
                    False
                Just l -> 
                    let l' = labelF k rs in
                    l `canFlowTo` l' && l' `canFlowTo` c
        
        convertRow :: Term -> ([(PrimaryKey, Label)], [(PrimaryKey, DBValue)])
        convertRow TNil = ([], [])
        convertRow (TCons (TPair (TInt c) (TLabeledTCB l v)) t) =
            let (ls, rs) = convertRow t in
            ( (c, l):ls, (c, DBValue v):rs)
        convertRow _ = error "unreachable"


evalProgram (Pg l c m (TInsert n rs)) | Just rs' <- evalRow rs = 
    Pg l c m (TInsert n rs')

evalProgram (Pg l c m (TInsert n rs)) | Map.lookup n m == Nothing = 
    Pg l c m TException

evalProgram (Pg l c m t@(TInsert n rs)) | Just Table{..} <- Map.lookup n m =
    -- Get fresh key.
    let k = freshKey tableRows in

    -- Convert row.
    let rs' = Row (Map.fromList (convertRow rs)) in

    -- Check label for each field.
    let tableCheck = l `canFlowTo` tableLabel && tableLabel `canFlowTo` c in
    let checks = Map.foldl (checkLabel k rs') tableCheck tableLabelFunctions in
    if checks then

        -- Insert row.
        let tableRows' = Map.insert k rs' tableRows in

        -- Update table.
        let m' = Map.insert n (Table tableRows' tableLabelFunctions tableLabel) m in

        Pg l c m' TUnit

    else
        Pg l c m TException

    where
        checkLabel _ _ False _ = False
        checkLabel k rs True (DBLabelFunction labelF) = 
            let l' = labelF k rs in
            l `canFlowTo` l' && l' `canFlowTo` c

        convertRow :: Term -> [(PrimaryKey, DBValue)]
        convertRow TNil = []
        convertRow (TCons (TPair (TInt c) v) t) = (c, DBValue v):(convertRow t)
        convertRow _ = error "unreachable"

evalProgram (Pg l c m (TSelect n fs)) = undefined

evalProgram (Pg l c m t) = Pg l c m (eval t)

-- Get a fresh key for the table.
freshKey :: Map PrimaryKey Row -> PrimaryKey
freshKey m = maybe 0 (\(k, _) -> k + 1) (Map.lookupMax m)

-- Take one step in a protected row. Returns Nothing if there are no more steps to take.
evalPRow :: Term -> Maybe Term
evalPRow TNil = Nothing
evalPRow (TCons h@(TPair (TInt _) (TLabeledTCB l v)) t) | isDatabaseValue v = fmap (TCons h) (evalRow t)
evalPRow (TCons (TPair c@(TInt _) (TLabeledTCB l v)) t) = Just (TCons (TPair c (TLabeledTCB l (eval v))) t)
evalPRow (TCons (TPair c@(TInt _) l) t) = Just (TCons (TPair c (eval l)) t)
evalPRow (TCons (TPair c l) t) = Just (TCons (TPair (eval c) l) t)
evalPRow (TCons h t) = Just (TCons (eval h) t)
evalPRow t = Just (eval t)

-- Take one step in the row. Returns Nothing if there are no more steps to take.
evalRow :: Term -> Maybe Term
evalRow TNil = Nothing
evalRow (TCons h@(TPair (TInt _) v) t) | isDatabaseValue v = fmap (TCons h) (evalRow t)
evalRow (TCons (TPair c@(TInt _) v) t) = Just (TCons (TPair c (eval v)) t)
evalRow (TCons (TPair c v) t) = Just (TCons (TPair (eval c) v) t)
evalRow (TCons h t) = Just (TCons (eval h) t)
evalRow t = Just (eval t)

isDatabaseValue :: Term -> Bool
isDatabaseValue TUnit = True
isDatabaseValue TTrue = True
isDatabaseValue TFalse = True
isDatabaseValue (TInt _) = True
isDatabaseValue (TVLabel _) = True
-- isDatabaseValue THole = True -- THole?
isDatabaseValue _ = False

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

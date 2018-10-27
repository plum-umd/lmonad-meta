{-@ LIQUID "--reflection"  @-}
{-# LANGUAGE CPP #-}
module Programs where

import Labels 

import Prelude hiding (Maybe(..), fromJust, isJust)
 

import ProofCombinators 


--- ... Grrrrrr if I just import all these, proofs break...
#include "Terms/IsValue.hs" 
#include "Terms/IsDBValue.hs" 
#include "Terms/IsPure.hs" 
#include "Terms/IsSafe.hs" 
#include "Terms/Termination.hs" 
#include "Terms/Terms.hs" 
#include "Terms/Erasure.hs" 
#include "Terms/Evaluation.hs" 
#include "DataBase/DataBase.hs" 

data Program l = PgHole {pHDB :: DB l}     | Pg {pLabel :: l, pgDB :: DB l, pTerm :: Term l }
{-@ data Program l = PgHole {pHDB :: DB l} | Pg {pLabel :: l, pgDB :: DB l, pTerm :: Term l } @-}


{-@ measure pDB @-}
pDB :: Program l -> DB l 
pDB (PgHole db) = db 
pDB (Pg _ db _) = db 

{-@ measure isPg @-}
isPg :: Program l -> Bool 
isPg (Pg _ _ _) = True 
isPg (PgHole _) = False 



{-@ measure isJust @-}
isJust :: Maybe a -> Bool 
isJust (Just _) = True 
isJust _        = False 


{-@ measure fromJust @-}
{-@ fromJust :: {x:Maybe a | Programs.isJust x } -> a @-}
fromJust :: Maybe a -> a 
fromJust (Just a) = a 


{-@ reflect lookupTableInfo @-}
lookupTableInfo :: TName -> DB l -> Maybe (TInfo l)
lookupTableInfo t db 
  = case lookupTable t db of 
     Nothing -> Nothing 
     Just (Table tinfo _) -> Just tinfo


{-@ reflect lookupTable @-}
lookupTable :: TName -> DB l -> Maybe (Table l) 
lookupTable t [] = Nothing 
lookupTable n ((Pair n' t):xs) 
  | n == n'
  = Just t 
  | otherwise 
  = lookupTable n xs 



{-@ reflect selectDB @-}
selectDB :: (Eq l, Label l) => DB l -> TName -> Pred l -> Term l 
{-@ selectDB :: (Eq l, Label l) => DB l -> TName -> Pred l -> STerm l @-}
selectDB [] n r = TNil  
selectDB ((Pair n' (Table tinfo rs)):xs) n p
  | n == n' 
  = selectRows p tinfo rs 
  | otherwise 
  = selectDB xs n p 

{-@ reflect selectRows @-}
{-@ selectRows :: (Eq l, Label l) => Pred l -> TInfo l -> [Row l] -> STerm l @-} 
selectRows :: (Eq l, Label l) => Pred l -> TInfo l -> [Row l] -> Term l 
selectRows p _ [] = TNil 
selectRows p tinfo (r@(Row k v1 v2):rs)
  | evalPred p r
  = TCons (rowToTerm tinfo r) 
          (selectRows p tinfo rs)
  | otherwise
  = selectRows p tinfo rs 


{-@ reflect rowToTerm @-}
{-@ rowToTerm :: (Eq l, Label l) => TInfo l -> Row l -> STerm l @-} 
rowToTerm :: (Eq l, Label l) => TInfo l -> Row l -> Term l 
rowToTerm tinfo (Row k v1 v2)
  = TCons (TLabeled (field1Label tinfo) v1) 
          (TCons (TLabeled (makeValLabel tinfo v1) v2) TNil) 

{-@ reflect evalPred @-}
evalPred :: Eq l => Pred l -> Row l -> Bool 
evalPred (Pred2 p) r
  = p (rowField1 r) (rowField2 r) -- evalPredicate p (Pair v1 v2)
evalPred (Pred1 p) r
  = p (rowField1 r)
evalPred (Pred0 p) _
  = p 


{-@ reflect updateDB @-}
updateDB :: Eq l => DB l -> TName -> Pred l -> Term l -> Term l -> DB l 
{-@ updateDB 
  :: DB l 
  -> TName 
  -> Pred l
  -> SDBTerm l 
  -> SDBTerm l  
  -> DB l @-} 
updateDB [] _ _ _ _ = [] 
updateDB ((Pair n' t@(Table ti rs)):ts) n p v1 v2  
  | n == n' 
  = Pair n (Table ti (updateRows p v1 v2 rs)):ts
  | otherwise 
  = Pair n' t:updateDB ts n p v1 v2  

{-@ reflect updateRows @-}
updateRows :: Eq l => Pred l -> Term l -> Term l -> [Row l] -> [Row l] 
{-@ updateRows 
  :: Pred l
  -> SDBTerm l 
  -> SDBTerm l 
  -> rs:[Row l] 
  -> [Row l] 
  / [len rs] @-} 
updateRows _ _ _ [] = [] 
updateRows p v1 v2 (r@(Row k _ _):rs)
  = updateRow p v1 v2 r :updateRows p v1 v2 rs


{-@ reflect updateRow @-}
updateRow :: Eq l => Pred l -> Term l -> Term l -> Row l -> Row l 
{-@ updateRow 
  :: Pred l
  -> SDBTerm l 
  -> SDBTerm l 
  -> rs:Row l 
  -> Row l @-} 
updateRow p v1 v2 r@(Row k _ _) = if evalPred p r then Row k v1 v2 else r 

{-@ reflect deleteDB @-}
deleteDB :: Eq l => DB l -> TName -> Pred l -> DB l 
deleteDB [] n p = [] 
deleteDB ((Pair n' t@(Table ti rs)):ts) n p
  | n == n' 
  = Pair n (Table ti (deleteRaws p rs)):ts
  | otherwise 
  = Pair n' t:deleteDB ts n p

{-@ reflect deleteRaws @-}
deleteRaws :: Eq l => Pred l -> [Row l] -> [Row l] 
deleteRaws _ [] = [] 
deleteRaws p (r:rs)
  | evalPred p r 
  = deleteRaws p rs 
  | otherwise
  = r:deleteRaws p rs  

{-@ reflect labelReadTable @-}
labelReadTable :: (Eq l, Label l) => Pred l -> TInfo l ->  l 
labelReadTable p ti | not (pDep1 p)
  = tableLabel ti
labelReadTable p ti  
  = tableLabel ti `join` field1Label ti 


{-@ reflect labelSelectTable @-}
labelSelectTable :: (Eq l, Label l) => Pred l -> Table l -> l 
labelSelectTable p (Table ti rs) = labelSelectRows p ti rs 

{-@ reflect labelSelectRows @-}
labelSelectRows :: (Eq l, Label l) => Pred l -> TInfo l -> [Row l] -> l 
labelSelectRows p ti []
  = tableLabel ti `join` field1Label ti
labelSelectRows p ti (r:rs) 
  = (tableLabel ti `join` labelPredRow p ti r) `join` labelSelectRows p ti rs



{-@ reflect updateLabelCheck @-}
updateLabelCheck :: (Label l, Eq l) => l -> Table l -> Pred l -> l -> Term l -> l -> Term l -> Bool 
updateLabelCheck lc t@(Table ti rs) p l1 v1 l2 v2  
  = updateRowsCheck lc (lfTable p t) ti p l1 v1 l2 v2 rs 


{-@ reflect updateRowsCheck @-}
updateRowsCheck :: (Label l, Eq l) => l -> l -> TInfo l -> Pred l -> l -> Term l -> l -> Term l -> [Row l] -> Bool 
{-@ updateRowsCheck :: (Label l, Eq l) => l -> l -> TInfo l -> Pred l -> l -> Term l -> l -> Term l -> rs:[Row l] -> Bool / [len rs] @-}
updateRowsCheck _ _ _ _ _ _ _ _ []            = True 
updateRowsCheck lc lφ ti p l1 v1 l2 v2 (r:rs) = updateRowCheck lc lφ ti p l1 v1 l2 v2 r && updateRowsCheck lc lφ ti p l1 v1 l2 v2 rs
-- XXX: now updateRowCheck does not depend on the row r
-- XXX: do the check even if the table is empty: then I do not need to raise to the table label

{-@ reflect updateRowCheck @-}
updateRowCheck :: (Label l, Eq l) => l -> l -> TInfo l -> Pred l -> l -> Term l -> l -> Term l -> Row l -> Bool 
updateRowCheck lc lφ ti p l1 v1 l2 v2 r 
  =  (updateRowLabel1 lc lφ ti p l1 v1 l2 v2 r)
   && (updateRowLabel2 lc lφ ti p l1 v1 l2 v2 r)


{-@ reflect updateRowLabel1 @-}
updateRowLabel1
  :: (Label l, Eq l)   
  => l -> l ->  TInfo l -> Pred l -> l -> Term l -> l -> Term l -> Row l 
  -> Bool  
updateRowLabel1 lc lφ ti p l1 v1 l2 v2 r -- @(Row _ o1 o2) 
  = if True {- (o1 /= v1) -} then 
     ((((l1 `join` lc) `join` lφ) `canFlowTo` field1Label ti) 
     )
     else True 

{-@ reflect updateRowLabel2 @-}
updateRowLabel2
  :: (Label l, Eq l)   
  => l -> l -> TInfo l -> Pred l -> l -> Term l -> l -> Term l -> Row l 
  -> Bool 
updateRowLabel2 lc lφ ti p l1 v1 l2 v2 r -- @(Row _ o1 o2)   
  = if True {- o2 /= v2-}  then 
       (((l2 `join` lc) `join` lφ) `canFlowTo` makeValLabel ti v1) else True  
    {- &&if True {- (makeValLabel ti o1  /=  makeValLabel ti v1)-}  then  
       (makeValLabel ti o1 `canFlowTo` makeValLabel ti v1) else True  -}


{-@ reflect lfTable @-}
lfTable  :: (Eq l, Label l) => Pred l -> Table l -> l 
lfTable p (Table ti rs) = lfRows p ti rs  

{-@ reflect lfRows @-}
lfRows  :: (Eq l, Label l) => Pred l -> TInfo l -> [Row l] -> l 
lfRows p ti []     = bot 
lfRows p ti (r:rs) = lfRow p ti r `join` lfRows p ti rs 


{-@ reflect lfRow @-}
lfRow  :: (Eq l, Label l) => Pred l -> TInfo l -> Row l -> l 
lfRow p ti r 
  | pDep2 p 
  = makeValLabel ti (rowField1 r)
  | pDep1 p 
  = field1Label ti
  | otherwise
  = bot 

{-@ reflect labelPredTable @-}
labelPredTable :: (Eq l, Label l) => Pred l -> Table l -> l 
labelPredTable p (Table ti rs) = labelPredRows p ti rs 


 

{-@ reflect labelPredRows @-}
labelPredRows :: (Eq l, Label l) => Pred l -> TInfo l -> [Row l] -> l 

labelPredRows p ti rs
  | not (pDep1 p)      
  = tableLabel ti
labelPredRows p ti []
  = tableLabel ti `join` field1Label ti
labelPredRows p ti (r:rs) 
  = (tableLabel ti `join` labelPredRow p ti r) `join` labelPredRows p ti rs

{-@ reflect labelPredRow @-}
labelPredRow :: (Eq l, Label l) => Pred l -> TInfo l -> Row l -> l 
labelPredRow p ti r 
  | pDep2 p 
  = field1Label ti `join` makeValLabel ti (rowField1 r)
labelPredRow _         ti r 
  = field1Label ti 


{-
{-@ reflect pDep2 @-}
pDep2 :: Pred -> Bool 
pDep2 p = pDependOn2 p 

{-@ reflect pDep1 @-}
pDep1 :: Pred -> Bool 
pDep1 p = pDependOn1 p 


{-@ reflect pVal @-}
pVal :: Pred -> Bool 
pVal p = pValue p 
-}

{-@ reflect insertDB @-}
insertDB :: DB l -> TName -> Row l -> DB l 
insertDB [] n r = [] 
insertDB ((Pair n' t):xs) n r
  | n == n' 
  = (Pair n (insertTable t r)):xs
  | otherwise 
  = (Pair n' t):insertDB xs n r 

{-@ reflect insertTable @-}
insertTable :: Table l -> Row l -> Table l 
insertTable (Table tinfo rs) r = Table tinfo (r:rs)


{-@ reflect eval @-}
{-@ eval 
     :: (Eq l, Label l) 
     => i:{Program l | terminates i } 
     -> { o:Program l | (isPg i => isPg o) && (ς i => ς o) }
      / [evalSteps i, 0] @-}

eval :: (Eq l, Label l) => Program l -> Program l
eval (PgHole db) 
  = PgHole db 

eval p@(Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2)))
  | not (ς p)
  = Pg lc db TException

eval p@(Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))) 
  | Just tinfo <- lookupTableInfo n db 
  -- , l' `canFlowTo` cc -- TODO
  , l1 `canFlowTo` field1Label tinfo
  , l2 `canFlowTo` (makeValLabel tinfo v1) 
  , lc `canFlowTo` tableLabel tinfo
  -- , isDBValue v1
  -- , isDBValue v2  
  = let i = uniquiInt tinfo in 
    let r = Row (TInt i) v1 v2 in 
    Pg l' (insertDB db n r) (TReturn (TInt i))
  where
    l' = l1 `join` lc

eval (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))) 
  = Pg l' db TException
  where
    l' = l1 `join` lc

-- TODO: the following cases should not be reached, so could get simplified
eval (Pg lc db (TInsert n t1@(TLabeled _ _) t2)) 
  = Pg lc db (TInsert n t1 (evalTerm t2))
eval (Pg lc db (TInsert n t1 t2))
  = Pg lc db (TInsert n (evalTerm t1) t2)

eval (Pg lc db (TDelete n (TPred p)))   
  | Just t <- lookupTable n db
  , (lc `join` labelPredTable p t) `canFlowTo` tableLabel (tableInfo t)   
  = Pg (lc `join` labelReadTable p (tableInfo t)) (deleteDB db n p) (TReturn TUnit)

eval (Pg lc db (TDelete n (TPred p)))   
  | Just t <- lookupTable n db
  = Pg (lc `join` labelReadTable p (tableInfo t)) db TException

eval (Pg lc db (TDelete n (TPred p)))   
  = Pg lc db TException
eval (Pg lc db (TDelete n t))
  = Pg lc db (TDelete n (evalTerm t))

eval (Pg lc db (TSelect n (TPred p)))   
  | Just t <- lookupTable n db 
  = Pg (lc `join` labelSelectTable p t) db (TReturn (selectDB db n p)) 
eval (Pg lc db (TSelect n (TPred p)))   
  = Pg lc db TException
eval (Pg lc db (TSelect n t))
  = Pg lc db (TSelect n (evalTerm t))


eval p@(Pg lc db (TUpdate _ _ _ _))   
  | not (ς p)
  = Pg lc db TException
eval (Pg lc db (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2)))   
  | Just t <- lookupTable n db 
  , updateLabelCheck lc t p l1 v1 l2 v2 
  = let lc' = lc `join` ((field1Label (tableInfo t) `join` l1) -- this is for TUpdateFound.C1
                         `join` tableLabel (tableInfo t))      -- this is for TUpdateFound.C2
    in 
    Pg lc' (updateDB db n p v1 v2) (TReturn TUnit)
eval (Pg lc db (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2)))   
  | Just t <- lookupTable n db 
  = let lc' = lc `join` ((field1Label (tableInfo t) `join` l1) `join` tableLabel (tableInfo t))  in 
    Pg lc' db (TReturn TException)
eval (Pg lc db (TUpdate n (TPred p) (TLabeled _ _) (TLabeled _ _)))   
  = Pg lc db TException

eval (Pg lc db (TUnlabel (TLabeled l t)))
  = Pg (lc `join` l) db (TReturn t)
eval (Pg lc db (TUnlabel t))
  = Pg lc db (evalTerm t)

eval (Pg lc db (TBind t1 t2))
  | Pg lc' db' (TLIO t1') <- evalStepsBindAxiom lc db t1 t2 `cast` 
                             evalStar (Pg lc db t1) 
  = Pg lc' db' (TApp t2 t1')
  | otherwise
  = Pg lc db TException

eval (Pg lc db (TReturn t))
  = Pg lc db (TLIO t)

eval (Pg lc db (TToLabeled (TVLabel ll) t))   
  | not (lc `canFlowTo` ll)
  = Pg lc db (TLIO TException)

eval (Pg lc db (TToLabeled (TVLabel ll) t))  
  | Pg lc' db' (TLIO t') <- evalStepsToLabeledAxiom lc db (TVLabel ll) t `cast` 
                            evalStar (Pg lc db t)
  , lc' `canFlowTo` ll
  = Pg lc db' (TLIO (TLabeled ll t'))   

eval (Pg lc db (TToLabeled (TVLabel ll) t))  
  | Pg _ db' _ <- evalStepsToLabeledAxiom lc db (TVLabel ll) t `cast`
                  evalStar (Pg lc db t)
  = Pg lc db' (TLIO (TLabeled ll TException))

eval (Pg lc db (TToLabeled t1 t2))
  = Pg lc db (TToLabeled (evalTerm t1) t2)

eval (Pg lc db (TLIO t)) 
  = Pg lc db (TLIO t)

eval (Pg lc db t) 
  = assert (isPure t) `cast` Pg lc db (evalTerm t)


{-@ reflect evalStar @-}
{-@ evalStar :: (Label l, Eq l) 
  => i:{Program l | terminates i }
  -> {o:Program l | (isPg i => isPg o) && (ς i => ς o)}
  / [evalSteps i, 1] @-}

evalStar :: (Label l, Eq l) => Program l -> Program l 
evalStar (PgHole db) 
  = PgHole db
evalStar (Pg lc db t) | isValue t 
  = Pg lc db t
evalStar p@(Pg lc db t)
  = evalStar (evalStepsAxiom p `cast` 
              eval p)  

{-@ reflect ε @-}
{-@ ε :: (Eq l, Label l) 
      => l 
      -> i:Program l 
      -> Program l @-}
ε :: (Eq l, Label l) =>  l -> Program l -> Program l
ε l (PgHole db) = PgHole (εDB l db)
ε l (Pg lc db t) 
  | not (lc `canFlowTo` l)
  = PgHole (εDB l db) 
ε l (Pg lc db t) 
  = Pg lc (εDB l db) (εTerm l t) 

{-@ LIQUID "--reflection"  @-}

module Simulations.TInsert0 where

import ProofCombinators
import Labels 
import Programs 

import Idempotence 
import Simulations.Terms 
import Simulations.Insert 
import Simulations.InsertAny
import TableInfoErase 
import DBValueErase 

import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsTInsertFound  
  :: Label l => l:l 
  -> lc:{l | canFlowTo lc l }
  -> db:DB l 
  -> n:TName 
  -> l1:l 
  -> v1:SDBTerm l
  -> l2:l 
  -> v2:{SDBTerm l | terminates (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2)))}
  -> tinfo:{TInfo l | (Just tinfo == lookupTableInfo n (εDB l db)) &&  (Just tinfo == lookupTableInfo n db) 
                    && (tinfo == fromJust (lookupTableInfo n (εDB l db))) && (isJust (lookupTableInfo n (εDB l db)))
                    && (tinfo == fromJust (lookupTableInfo n db)) && (isJust (lookupTableInfo n db)) }
  -> { ε l (eval (ε l (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))) == ε l (eval (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))  } 
  @-}
simulationsTInsertFound :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> l -> Term l -> l -> Term l -> TInfo l -> Proof

simulationsTInsertFound l lc db n l1 v1 l2 v2 tinfo
  | a
  && (l2 `canFlowTo` (makeValLabel tinfo v1))
  && not (l1 `canFlowTo` l)
  && not (l2 `canFlowTo` (makeValLabel tinfo THole))  = 
      ε l (eval (ε l (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TInsert n (εTerm l (TLabeled l1 v1)) (εTerm l (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TInsert n (TLabeled l1 v1') (TLabeled l2 v2')))) 
  ==. ε l (Pg l' (εDB l db) TException)
      ? joinCanFlowTo l1 lc l 
  ==. PgHole (εDB l (εDB l db))
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
      ? lawFlowTransitivity l1 (field1Label tinfo) (tableLabel tinfo) 
      ? lawFlowTransitivity l1 (tableLabel tinfo) l 
      ? assert (not (tableLabel tinfo `canFlowTo` l))
      ? simulationsInsertAny l db n r tinfo
      ? assert (εDB l (insertDB db n r) == εDB l db)
  ==. PgHole (εDB l (insertDB db n r))
  ==. ε l (Pg l' (insertDB db n r) (TReturn (TInt i)))
  ==. ε l (eval (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))
  *** QED 
  | a && (l2 `canFlowTo` (makeValLabel tinfo v1))
  =   ε l (eval (ε l (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TInsert n (εTerm l (TLabeled l1 v1)) (εTerm l (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TInsert n (TLabeled l1 v1') (TLabeled l2 v2')))) 
  ==. ε l (Pg l' (insertDB (εDB l db) n r') (TReturn (TInt i)))
      ? joinCanFlowTo l1 lc l 
  ==. (if l1 `canFlowTo` l 
         then Pg l'  (εDB l (insertDB (εDB l db) n r')) (εTerm l (TReturn (TInt i)))
         else PgHole (εDB l (insertDB (εDB l db) n r')))
      ? inserDBTableErase l n db r'
      ? insertDBRowErase l n db tinfo r'
      ? lawFlowTransitivity l1 (field1Label tinfo) l 
      ? lawFlowTransitivity l2 (makeValLabel tinfo v1) l 
      ? assert (εRow l tinfo r == εRow l tinfo r')
      ? insertDBRowErase l n db tinfo r  
  ==. (if l1 `canFlowTo` l 
         then Pg l'  (εDB l (insertDB db n r)) (εTerm l (TReturn (TInt i)))
         else PgHole (εDB l (insertDB db n r)))
  ==. ε l (Pg l' (insertDB db n r) (TReturn (TInt i)))
  ==. ε l (eval (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))
  *** QED  

    |  a 
    && not (l2 `canFlowTo` (makeValLabel tinfo v1))
    && not (l1 `canFlowTo` l) 
    && l2 `canFlowTo` (makeValLabel tinfo THole)
    =   ε l (eval (ε l (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2)))))
    ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TInsert n (TLabeled l1 v1) (TLabeled l2 v2)))))
    ==. ε l (eval (Pg lc (εDB l db) (TInsert n (εTerm l (TLabeled l1 v1)) (εTerm l (TLabeled l2 v2)))))
    ==. ε l (eval (Pg lc (εDB l db) (TInsert n (TLabeled l1 v1') (TLabeled l2 v2'))))
    ==. ε l (Pg l' (insertDB (εDB l db) n r') (TReturn (TInt i)))
        ? joinCanFlowTo l1 lc l 
    ==. PgHole (εDB l (insertDB (εDB l db) n r')) 
        ? inserDBTableErase l n db r' 
    ==. PgHole (εDB l (insertDB db n r')) 
        ? assert (field1Label tinfo `canFlowTo` tableLabel tinfo)
        ? lawFlowTransitivity l1 (field1Label tinfo) (tableLabel tinfo) 
        ? lawFlowTransitivity l1 (tableLabel tinfo) l 
        ? assert (not (tableLabel tinfo `canFlowTo` l))
        ? simulationsInsertAny l db n r' tinfo
        ? assert (εDB l (insertDB db n r') == εDB l db)
    ==. PgHole (εDB l db)
    ==. ε l (Pg l' db TException)
    ==. ε l (eval (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))
    *** QED

    | otherwise   
    =   ε l (eval (ε l (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2)))))
    ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TInsert n (TLabeled l1 v1) (TLabeled l2 v2)))))
    ==. ε l (eval (Pg lc (εDB l db) (TInsert n (εTerm l (TLabeled l1 v1)) (εTerm l (TLabeled l2 v2)))))
    ==. ε l (eval (Pg lc (εDB l db) (TInsert n (TLabeled l1 v1') (TLabeled l2 v2')))) 
    ==. ε l (Pg l' (εDB l db) TException)
        ? eraseDB l l' db TException
    ==. ε l (Pg l' db TException)
    ==. ε l (eval (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))
    *** QED 
  where
    i   = uniquiInt tinfo    
    l'  = l1 `join` lc
    r   = Row (TInt i) v1 v2
    v1' = if l1 `canFlowTo` l then εTerm l v1 else THole
    v2' = if l2 `canFlowTo` l then εTerm l v2 else THole
    r'  = Row (TInt i) v1' v2'

    a =  (l1 `canFlowTo` field1Label tinfo)  
      && (lc `canFlowTo` tableLabel tinfo)


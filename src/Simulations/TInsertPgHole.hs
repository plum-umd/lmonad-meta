{-@ LIQUID "--reflection"        @-}

module Simulations.TInsertPgHole where

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

{-@ simulationsTInsert  
  :: Label l => l:l 
  -> lc:{l | not (canFlowTo lc l) }
  -> db:DB l 
  -> n:TName 
  -> t1:Term l
  -> t2:{Term l | ς (Pg lc db (TInsert n t1 t2)) && terminates (Pg lc db (TInsert n t1 t2))}
  -> { ε l (eval (ε l (Pg lc db (TInsert n t1 t2)))) == ε l (eval (Pg lc db (TInsert n t1 t2))) } 
  @-}
simulationsTInsert :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Term l -> Term l -> Proof

simulationsTInsert l lc db n (TLabeled l1 v1) (TLabeled l2 v2)
  =   assert (ς (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))
  &&& assert (isDBValue v1) &&& assert (isDBValue v2)
  &&& simulationsTInsert' l lc db n l1 v1 l2 v2

simulationsTInsert l lc db n t1@(TLabeled l1 v1) t2
  =   ε l (eval (ε l (Pg lc db (TInsert n t1 t2))))
  ==. ε l (eval (PgHole (εDB l db)))
  ==. ε l (PgHole (εDB l db))
  ==. PgHole (εDB l (εDB l db))
       ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
  ==. ε l (Pg lc db (TInsert n t1 (evalTerm t2)))
  ==. ε l (eval (Pg lc db (TInsert n t1 t2)))
  *** QED  


simulationsTInsert l lc db n t1 t2
  =   ε l (eval (ε l (Pg lc db (TInsert n t1 t2))))
  ==. ε l (eval (PgHole (εDB l db)))
  ==. ε l (PgHole (εDB l db))
  ==. PgHole (εDB l (εDB l db))
       ? εDBIdempotent l db
  ==. PgHole (εDB l db)
  ==. ε l (Pg lc db (TInsert n (evalTerm t1) t2))
  ==. ε l (eval (Pg lc db (TInsert n t1 t2)))
  *** QED  


{-@ simulationsTInsert'  
  :: Label l => l:l 
  -> lc:{l | not (canFlowTo lc l) }
  -> db:DB l 
  -> n:TName 
  -> l1:l 
  -> v1:{t:Term l | isDBValue t && ςTerm t }
  -> l2:l 
  -> v2:{Term l | isDBValue v2 && ςTerm v2 && terminates (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2)))}
  -> { ε l (eval (ε l (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))) == ε l (eval (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))  } 
  @-}
simulationsTInsert' :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> l -> Term l -> l -> Term l -> Proof

simulationsTInsert' l lc db n l1 v1 l2 v2
  | Just tinfo <- lookupTableInfo n (εDB l db)
  =   lookupTableInfoErase l n db 
  &&& simulationsTInsertFound l lc db n l1 v1 l2 v2 tinfo 


simulationsTInsert' l lc db n l1 v1 l2 v2 
    | Nothing <- lookupTableInfo n (εDB l db)
    =   ε l (eval (ε l (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2)))))
    ==. ε l (eval (PgHole (εDB l db)))
    ==. ε l (PgHole (εDB l db))
    ==. PgHole (εDB l (εDB l db))
       ? εDBIdempotent l db
    ==. PgHole (εDB l (εDB l db))
        ? joinCanFlowTo l1 lc l 
    ==. ε l (Pg (l1 `join` lc) db TException)
        ? lookupTableInfoErase l n db
    ==. ε l (eval (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))
    *** QED


{-@ simulationsTInsertFound  
  :: Label l => l:l 
  -> lc:{l | not (canFlowTo lc l) }
  -> db:DB l 
  -> n:TName 
  -> l1:l 
  -> v1:{t:Term l | isDBValue t && ςTerm t } 
  -> l2:l 
  -> v2:{Term l | isDBValue v2 && ςTerm v2 && terminates (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2)))}
  -> tinfo:{TInfo l | (Just tinfo == lookupTableInfo n (εDB l db)) &&  (Just tinfo == lookupTableInfo n db) 
                    && (tinfo == fromJust (lookupTableInfo n (εDB l db))) && (isJust (lookupTableInfo n (εDB l db)))
                    && (tinfo == fromJust (lookupTableInfo n db)) && (isJust (lookupTableInfo n db)) }
  -> { ε l (eval (ε l (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))) == ε l (eval (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))  } 
  @-}
simulationsTInsertFound :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> l -> Term l -> l -> Term l -> TInfo l -> Proof

simulationsTInsertFound l lc db n l1 v1 l2 v2 tinfo
  | a && (l2 `canFlowTo` (makeValLabel tinfo v1))
  =   ε l (eval (ε l (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))) 
  ==. ε l (eval (PgHole (εDB l db)))
  ==. ε l (PgHole (εDB l db))
  ==. PgHole (εDB l (εDB l db))
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
      ? lawFlowTransitivity lc (tableLabel tinfo) l 
      ? simulationsInsertAny l db n r tinfo
  ==. PgHole (εDB l (insertDB db n r))
      ? joinCanFlowTo l1 lc l 
  ==. ε l (Pg l' (insertDB db n r) (TReturn (TInt i)))
  ==. ε l (eval (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))
  *** QED  

  | not a || not (l2 `canFlowTo` (makeValLabel tinfo v1))
  =   ε l (eval (ε l (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))) 
  ==. ε l (eval (PgHole (εDB l db)))
  ==. ε l (PgHole (εDB l db))
  ==. PgHole (εDB l (εDB l db))
      ? εDBIdempotent l db
  ==. PgHole (εDB l db)
      ? joinCanFlowTo l1 lc l 
  ==. ε l (Pg l' db TException)
  ==. ε l (eval (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))
  *** QED  
  where
    i   = uniquiInt tinfo    
    l'  = l1 `join` lc
    r   = Row (TInt i) v1 v2

    a =  (l1 `canFlowTo` field1Label tinfo)  
      && (lc `canFlowTo` tableLabel tinfo)



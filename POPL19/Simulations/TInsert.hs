{-@ LIQUID "--reflection"        @-}

module Simulations.TInsert where

import ProofCombinators
import Labels 
import Programs 

import Idempotence 
import Simulations.Terms 
import Simulations.TInsert0 
import Simulations.Insert 
import TableInfoErase 
import DBValueErase
import SafeDBValues
import SafeErase

import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsTInsert  
  :: Label l => l:l 
  -> lc:{l | canFlowTo lc l }
  -> db:DB l 
  -> n:TName 
  -> t1:Term l
  -> t2:{Term l | ς (Pg lc db (TInsert n t1 t2)) && terminates (Pg lc db (TInsert n t1 t2))}
  -> { ε l (eval (ε l (Pg lc db (TInsert n t1 t2)))) == ε l (eval (Pg lc db (TInsert n t1 t2))) } 
  @-}
simulationsTInsert :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Term l -> Term l -> Proof

simulationsTInsert l lc db n (TLabeled l1 v1) (TLabeled l2 v2)
  = assert (ς (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))
  &&& assert (isDBValue v1) &&& assert (isDBValue v2)
  &&& simulationsTInsert' l lc db n l1 v1 l2 v2

simulationsTInsert l lc db n t1@(TLabeled l1 v1) t2
  =   ε l (eval (ε l (Pg lc db (TInsert n t1 t2))))
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TInsert n t1 t2))))
  ==. ε l (eval (Pg lc (εDB l db) (TInsert n (εTerm l t1) (εTerm l t2))))
  ==. ε l (eval (Pg lc (εDB l db) (TInsert n (TLabeled l1 v1') (εTerm l t2))))
  ==. ε l (Pg lc (εDB l db) (TInsert n (TLabeled l1 v1') (evalTerm (εTerm l t2))))
  ==. Pg lc (εDB l (εDB l db)) (εTerm l (TInsert n (TLabeled l1 v1') (evalTerm (εTerm l t2))))
  ==. Pg lc (εDB l (εDB l db)) (TInsert n (εTerm l (TLabeled l1 v1')) (εTerm l (evalTerm (εTerm l t2))))
  ==. Pg lc (εDB l (εDB l db)) (TInsert n (εTerm l (εTerm l t1)) (εTerm l (evalTerm (εTerm l t2))))
       ? εDBIdempotent l db &&& simulationsTerm l t2 &&& εTermIdempotent l t1 
  ==. Pg lc (εDB l db) (TInsert n (εTerm l t1) (εTerm l (evalTerm t2)))
  ==. Pg lc (εDB l db) (εTerm l (TInsert n t1 (evalTerm t2)))
  ==. ε l (Pg lc db (TInsert n t1 (evalTerm t2)))
  ==. ε l (eval (Pg lc db (TInsert n t1 t2)))
  *** QED  
  where
    v1' = if l1 `canFlowTo` l then (εTerm l v1) else THole


simulationsTInsert l lc db n t1 t2
  =   ε l (eval (ε l (Pg lc db (TInsert n t1 t2))))
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TInsert n t1 t2))))
  ==. ε l (eval (Pg lc (εDB l db) (TInsert n (εTerm l t1) (εTerm l t2))))
  ==. ε l (Pg lc (εDB l db) (TInsert n (evalTerm (εTerm l t1)) (εTerm l t2)))
  ==. Pg lc (εDB l (εDB l db)) (εTerm l (TInsert n (evalTerm (εTerm l t1)) (εTerm l t2)))
  ==. Pg lc (εDB l (εDB l db)) (TInsert n (εTerm l (evalTerm (εTerm l t1))) (εTerm l (εTerm l t2)))
       ? εDBIdempotent l db &&& simulationsTerm l t1 &&& εTermIdempotent l t2
  ==. Pg lc (εDB l db)         (TInsert n (εTerm l (evalTerm t1)) (εTerm l t2))
  ==. Pg lc (εDB l db) (εTerm l (TInsert n (evalTerm t1) t2))
  ==. ε l (Pg lc db (TInsert n (evalTerm t1) t2))
  ==. ε l (eval (Pg lc db (TInsert n t1 t2)))
  *** QED  


{-@ simulationsTInsert'  
  :: Label l => l:l 
  -> lc:{l | canFlowTo lc l }
  -> db:DB l 
  -> n:TName 
  -> l1:l 
  -> v1:SDBTerm l 
  -> l2:l 
  -> v2:{SDBTerm l | terminates (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2)))}
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
    ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TInsert n (TLabeled l1 v1) (TLabeled l2 v2)))))
    ==. ε l (eval (Pg lc (εDB l db) (TInsert n (εTerm l (TLabeled l1 v1)) (εTerm l (TLabeled l2 v2)))))
    ==. ε l (eval (Pg lc (εDB l db) (TInsert n (TLabeled l1 v1') (TLabeled l2 v2'))))
        ? safeErase l (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2)))
        ? safeDBValue v1'
        ? safeDBValue v2'
        ? assert (ςTerm (TInsert n (TLabeled l1 v1') (TLabeled l2 v2')))
        ? assert (ς (Pg lc (εDB l db) (TInsert n (TLabeled l1 v1') (TLabeled l2 v2'))))

    ==. ε l (Pg l' (εDB l db) TException)
        
        ? eraseDB l l' db TException

    ==. ε l (Pg l' db TException)
        ? lookupTableInfoErase l n db
        ? safeDBValue v1
        ? safeDBValue v2
    ==. ε l (eval (Pg lc db (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))))
    *** QED

  where
    l' = l1 `join` lc
    v1' = if l1 `canFlowTo` l then εTerm l v1 else THole
    v2' = if l2 `canFlowTo` l then εTerm l v2 else THole


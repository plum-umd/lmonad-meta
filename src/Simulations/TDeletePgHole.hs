{-@ LIQUID "--reflection"  @-}

module Simulations.TDeletePgHole where

import ProofCombinators
import Labels 
import Programs 

import Idempotence 
import qualified LookupTableErase 
import LabelPredErase 
import Simulations.Terms 

import Simulations.Delete 
import Simulations.DeleteAll 
import Simulations.DeleteHelpers

import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsTDelete  
  :: Label l => l:l 
  -> lc:{l | not (canFlowTo lc l) }
  -> db:DB l 
  -> n:TName 
  -> t:{Term l | terminates (Pg lc db (TDelete n t))}
  -> { ε l (eval (ε l (Pg lc db (TDelete n t)))) == ε l (eval (Pg lc db (TDelete n t))) } 
  @-}
simulationsTDelete :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Term l -> Proof

simulationsTDelete l lc db n (TPred p) 
  | Just t  <- lookupTable n db 
  , Just εt <- lookupTable n (εDB l db) 
  = LookupTableErase.lookupTableErase l n db &&& labelPredErase l p n db &&& simulationsTDeleteFound l lc db n p t εt

simulationsTDelete l lc db n (TPred p) 
  | Just t <- lookupTable n db
  = LookupTableErase.lookupTableErase l n db 
  ? assert False   


simulationsTDelete l lc db n (TPred p) 
  | Just t <- lookupTable n (εDB l db) 
  = LookupTableErase.lookupTableErase l n db 
  ? assert False   


simulationsTDelete l lc db n (TPred p) 
  =   ε l (eval (ε l (Pg lc db (TDelete n (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TDelete n (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TDelete n (εTerm l (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TDelete n (TPred p))))
  ==. ε l (Pg lc (εDB l db) TException) 
  ==. PgHole (εDB l (εDB l db)) 
      ? εDBIdempotent l db  
  ==. PgHole (εDB l db) 
  ==. ε l (Pg lc db TException) 
  ==. ε l (eval (Pg lc db (TDelete n (TPred p)))) 
  *** QED 

simulationsTDelete l lc db n t 
  =   ε l (eval (ε l (Pg lc db (TDelete n t)))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TDelete n t)))) 
  ==. ε l (eval (Pg lc (εDB l db) (TDelete n (εTerm l t)))) 
  ==. ε l (eval (Pg lc (εDB l db) (TDelete n (εTerm l t)))) 
  ==. ε l (Pg lc (εDB l db) (TDelete n (evalTerm (εTerm l t)))) 
  ==. Pg lc (εDB l (εDB l db)) (εTerm l (TDelete n (evalTerm (εTerm l t)))) 
  ==. Pg lc (εDB l (εDB l db)) (εTerm l (TDelete n (evalTerm (εTerm l t)))) 
  ==. Pg lc (εDB l (εDB l db)) (TDelete n (εTerm l (evalTerm (εTerm l t))))
      ? simulationsTerm l t &&& εDBIdempotent l db  
  ==. Pg lc (εDB l db) (TDelete n (εTerm l (evalTerm t)))
  ==. Pg lc (εDB l db) (εTerm l (TDelete n  (evalTerm t)))
  ==. ε l (Pg lc db (TDelete n (evalTerm t))) 
  ==. ε l (eval (Pg lc db (TDelete n t))) 
  *** QED 


{-@ simulationsTDeleteFound  
  :: Label l => l:l 
  -> lc:{l | not (canFlowTo lc l) }
  -> db:DB l 
  -> n:TName 
  -> p:{Pred | terminates (Pg lc db (TDelete n (TPred p)))}
  -> t :{Table l | Just  t == lookupTable n db }
  -> εt:{Table l |  (Just εt == lookupTable n (εDB l db)) 
                 && (tableInfo t == tableInfo εt)
                 && (canFlowTo (labelPredTable p t) l <=> canFlowTo (labelPredTable p εt) l)
                 }
  -> { ε l (eval (ε l (Pg lc db (TDelete n (TPred p))))) == ε l (eval (Pg lc db (TDelete n (TPred p)))) } 
  @-}
simulationsTDeleteFound :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> Table l -> Table l -> Proof

simulationsTDeleteFound l lc db n p t εt
  | a, c, b, εb
  =   ε l (eval (ε l (Pg lc db (TDelete n (TPred p))))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db))
  ==. PgHole (εDB l (εDB l db))
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
      ? lawFlowTransitivity lc lt l 
      ? simulationsDeleteAll l db n p t 
  ==. PgHole (εDB l (deleteDB db n p)) 
      ? joinCanFlowTo lc lr l 
  ==. ε l (Pg (lc `join` lr)  (deleteDB db n p) (TReturn TUnit)) 
      ? joinCanFlowTo lc lp lt 
  ==. ε l (eval (Pg lc db (TDelete n (TPred p)))) 
  *** QED 

  | (not c && not b && not εb)
  || not a 
  || (a && c && not b && not εb)
  =   ε l (eval (ε l (Pg lc db (TDelete n (TPred p))))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db))
  ==. PgHole (εDB l (εDB l db))
      ? εDBIdempotent l db
  ==. PgHole (εDB l db)
      ? joinCanFlowTo lc lr l 
      ? unjoinCanFlowTo lc lr l 
  ==. ε l (Pg (lc `join` lr)  db         TException) 
      ? unjoinCanFlowTo lc lp lt 
  ==. ε l (eval (Pg lc db (TDelete n (TPred p)))) 
  *** QED 

  | a && not c && b && εb && not (lt `canFlowTo` l)
  =   ε l (eval (ε l (Pg lc db (TDelete n (TPred p))))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db)) 
  ==. PgHole (εDB l (εDB l db)) 
      ? εDBIdempotent l db
      ? lawFlowTransitivity lc lt l 
      ? simulationsDeleteAll l db n p t 
  ==. PgHole (εDB l (deleteDB db n p))
      ? joinCanFlowTo lc lr l 
  ==. ε l (Pg (lc `join` lr)  (deleteDB db n p) (TReturn TUnit)) 
      ? joinCanFlowTo lc lp lt  
  ==. ε l (eval (Pg lc db (TDelete n (TPred p))))   
  *** QED 

  | not c && not (lt `canFlowTo` l), b, not εb 
  =   ε l (eval (ε l (Pg lc db (TDelete n (TPred p))))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db)) 
  ==. PgHole (εDB l (εDB l db))
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
      ? lawFlowTransitivity lc lt l 
      ? simulationsDeleteAll l db n p t 
  ==. PgHole (εDB l (deleteDB db n p))
      ? joinCanFlowTo lc lr l 
  ==. ε l (Pg (lc `join` lr)  (deleteDB db n p) (TReturn TUnit)) 
      ? joinCanFlowTo lc lp lt  
  ==. ε l (eval (Pg lc db (TDelete n (TPred p))))   
  *** QED 

  | not c && not (lt `canFlowTo` l), not b, εb 
  =   ε l (eval (ε l (Pg lc db (TDelete n (TPred p))))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db)) 
  ==. PgHole (εDB l (εDB l db)) 
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
      ? joinCanFlowTo lc lr l 
  ==. ε l (Pg (lc `join` lr)  db TException) 
      ? joinCanFlowTo lc lp lt  
  ==. ε l (eval (Pg lc db (TDelete n (TPred p))))   
  *** QED 

  where 
   ti  = tableInfo t          
   εti = tableInfo εt         `const` assert (tableInfo εt == tableInfo t) 
   lp  = labelPredTable p t
   εlp = labelPredTable p εt
   lr  = labelReadTable p ti

   lt  = tableLabel ti 

   a   = lc  `canFlowTo` lt 
   c   = lr  `canFlowTo` l    
   b   = lp  `canFlowTo` lt 
   εb  = εlp `canFlowTo` lt  
         `const` assert (lookupTable n (εDB l db) == Just (εTable l t) 
                         ? assert (isJust (Just t))
                         ? assert (isJust (lookupTable n db))
                         ? lookupTableErase l db n t)
         `const` assert (if c then lp == εlp ? labelPredTableEraseEq l p t else True)
         `const` labelPredTableErase l p t 
         `const` labelPredTableErase l p (εTable l t)




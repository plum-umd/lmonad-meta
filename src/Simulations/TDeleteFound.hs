{-@ LIQUID "--reflection"  @-}

module Simulations.TDeleteFound where

import ProofCombinators
import Labels 
import Programs 

import Idempotence 
import Simulations.Terms 
import Simulations.Delete 
import Simulations.DeleteAll 
import Simulations.DeleteHelpers 

import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsTDeleteFound  
  :: Label l => l:l 
  -> lc:{l | canFlowTo lc l }
  -> db:DB l 
  -> n:TName 
  -> p:{Pred l | terminates (Pg lc db (TDelete n (TPred p)))}
  -> t :{Table l | Just  t == lookupTable n db }
  -> εt:{Table l |  (Just εt == lookupTable n (εDB l db)) 
                 && (tableInfo t == tableInfo εt)
                 && (canFlowTo (labelPredTable p t) l <=> canFlowTo (labelPredTable p εt) l)
                 }
  -> { ε l (eval (ε l (Pg lc db (TDelete n (TPred p))))) == ε l (eval (Pg lc db (TDelete n (TPred p)))) } 
  @-}
simulationsTDeleteFound :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred l -> Table l -> Table l -> Proof


simulationsTDeleteFound l lc db n p t εt
  | a && c && b && εb
  =   ε l (eval (ε l (Pg lc db (TDelete n (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TDelete n (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TDelete n (εTerm l (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TDelete n (TPred p))))
      ? joinCanFlowTo lc lp lt 
  ==. ε l (Pg (lc `join` lr) (deleteDB (εDB l db) n p) (TReturn TUnit))
      ? joinCanFlowTo lc lr l 
  ==. Pg (lc `join` lr) (εDB l (deleteDB (εDB l db) n p)) (εTerm l (TReturn TUnit))
      ? labelReadFlowsToTableLabel l p ti 
      ? lawFlowTransitivity lp lt l 
      ? assert (canFlowTo lp l)
      ? simulationsDelete l db n p t 
  ==. Pg (lc `join` lr)  (εDB l (deleteDB db n p)) (εTerm l (TReturn TUnit)) 
      ? joinCanFlowTo lc lr l 
  ==. ε l (Pg (lc `join` lr)  (deleteDB db n p) (TReturn TUnit)) 
      ? joinCanFlowTo lc lp lt 
  ==. ε l (eval (Pg lc db (TDelete n (TPred p)))) 
  *** QED 

  | (not c && not b && not εb)
  || not a 
  || (a && c && not b && not εb)
  =   ε l (eval (ε l (Pg lc db (TDelete n (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TDelete n (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TDelete n (εTerm l (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TDelete n (TPred p))))
      ? unjoinCanFlowTo lc εlp lt 
  ==. ε l (Pg (lc `join` lr) (εDB l db) TException)
      ? joinCanFlowTo lc lr l       
      ? unjoinCanFlowTo lc lr l 
  ==. (if c then Pg (lc `join` lr) (εDB l (εDB l db)) (εTerm l TException)
            else PgHole (εDB l (εDB l db)))
      ? εDBIdempotent l db
  ==. (if c then Pg (lc `join` lr)  (εDB l db)         (εTerm l TException) 
            else PgHole (εDB l db))
      ? joinCanFlowTo lc lr l 
      ? unjoinCanFlowTo lc lr l 
  ==. ε l (Pg (lc `join` lr)  db         TException) 
      ? unjoinCanFlowTo lc lp lt 
  ==. ε l (eval (Pg lc db (TDelete n (TPred p)))) 
  *** QED 

  | a && not c && b && εb && not (lt `canFlowTo` l)
  =   ε l (eval (ε l (Pg lc db (TDelete n (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TDelete n (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TDelete n (εTerm l (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TDelete n (TPred p))))
      ? joinCanFlowTo lc εlp lt 
  ==. ε l (Pg (lc `join` lr) (deleteDB (εDB l db) n p) (TReturn TUnit))
      ? joinCanFlowTo lc lr l
  ==. PgHole (εDB l (deleteDB (εDB l db) n p))
      ? simulationsDeleteAll l db n p t 
  ==. PgHole (εDB l (deleteDB db n p))
  ==. ε l (Pg (lc `join` lr)  (deleteDB db n p) (TReturn TUnit)) 
      ? joinCanFlowTo lc lp lt  
  ==. ε l (eval (Pg lc db (TDelete n (TPred p))))   
  *** QED 

  | not c && not (lt `canFlowTo` l) && b && not εb 
  =   ε l (eval (ε l (Pg lc db (TDelete n (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TDelete n (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TDelete n (εTerm l (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TDelete n (TPred p))))
      ? joinCanFlowTo lc εlp lt 
  ==. ε l (Pg (lc `join` lr) (εDB l db) TException)
      ? joinCanFlowTo lc lr l
  ==. PgHole (εDB l (εDB l db))
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
      ? simulationsDeleteAll l db n p t 
  ==. PgHole (εDB l (deleteDB db n p))
  ==. ε l (Pg (lc `join` lr)  (deleteDB db n p) (TReturn TUnit)) 
      ? joinCanFlowTo lc lp lt  
  ==. ε l (eval (Pg lc db (TDelete n (TPred p))))   
  *** QED 

  | not c && not (lt `canFlowTo` l) && not b && εb 
  =   ε l (eval (ε l (Pg lc db (TDelete n (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TDelete n (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TDelete n (εTerm l (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TDelete n (TPred p))))
      ? joinCanFlowTo lc εlp lt 
  ==. ε l (Pg (lc `join` lr) (deleteDB (εDB l db) n p) (TReturn TUnit))
      ? joinCanFlowTo lc lr l
  ==. PgHole (εDB l (deleteDB (εDB l db) n p))
      ? simulationsDeleteAll l db n p t 
  ==. PgHole (εDB l db)
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



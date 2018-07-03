{-@ LIQUID "--reflection"  @-}

module Simulations.TDelete where

import ProofCombinators
import Labels 
import Programs 
import Predicates 

import Idempotence 
import LookupTableErase 
import LabelPredErase
import Simulations.Terms 
import Simulations.TDeleteFound 


import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsTDelete  
  :: Label l => l:l 
  -> lc:{l | canFlowTo lc l }
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
  = lookupTableErase l n db &&& labelPredErase l p n db &&& simulationsTDeleteFound l lc db n p t εt

simulationsTDelete l lc db n (TPred p) 
  | Just t <- lookupTable n db
  = lookupTableErase l n db 
  ? assert False   


simulationsTDelete l lc db n (TPred p) 
  | Just t <- lookupTable n (εDB l db) 
  = lookupTableErase l n db 
  ? assert False   


simulationsTDelete l lc db n (TPred p) 
  =   ε l (eval (ε l (Pg lc db (TDelete n (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TDelete n (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TDelete n (εTerm l (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TDelete n (TPred p))))
  ==. ε l (Pg lc (εDB l db) TException) 
  ==. Pg lc (εDB l (εDB l db)) (εTerm l TException)
      ? εDBIdempotent l db  
  ==. Pg lc (εDB l db) (εTerm l TException)
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

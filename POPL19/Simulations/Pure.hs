{-@ LIQUID "--reflection"  @-}

module Simulations.Pure where

import ProofCombinators
import Labels 
import Programs 

import Idempotence 
import Purity 
import Simulations.Terms 

import Prelude hiding (Maybe(..), fromJust, isJust)


{-@ simulationsPure  
  :: Label l => l:l 
  -> lc:l
  -> db:DB l 
  -> t:{Term l | isPure t && terminates (Pg lc db t) }  
  -> { ε l (eval (ε l (Pg lc db t))) == ε l (eval (Pg lc db t)) } 
  @-}
simulationsPure :: (Label l, Eq l) 
  => l -> l -> DB l -> Term l -> Proof

simulationsPure l lc db t
  | lc `canFlowTo` l 
  =   ε l (eval (ε l (Pg lc db t)))
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l t)))
      ? pureProp l db t
      ? pureProp lc (εDB l db) (εTerm l t)
  ==. ε l (Pg lc (εDB l db) (evalTerm (εTerm l t)))
  ==. Pg lc (εDB l (εDB l db)) (εTerm l (evalTerm (εTerm l t)))
      ? simulationsTerm l t &&& εDBIdempotent l db 
  ==. Pg lc (εDB l db) (εTerm l (evalTerm t))  
  ==. ε l (Pg lc db (evalTerm t)) 
      ? pureProp lc db t  
  ==. ε l (eval (Pg lc db t))  
  *** QED    
  | otherwise  
  =   ε l (eval (ε l (Pg lc db t)))
  ==. ε l (eval (PgHole (εDB l db)))
  ==. ε l (PgHole (εDB l db))
  ==. PgHole (εDB l (εDB l db)) 
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
  ==. ε l (PgHole db )  
  ==. ε l (Pg lc db (evalTerm t))  
      ? pureProp lc db t 
  ==. ε l (eval (Pg lc db t))  
  *** QED 
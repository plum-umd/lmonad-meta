{-@ LIQUID "--reflection"        @-}

module Simulations.TBind where

import ProofCombinators
import Labels 
import Programs 

import Prelude hiding (Maybe(..), fromJust, isJust)
{-@ simulationsBind 
  :: l:l
  -> lc:{l | canFlowTo lc l} 
  -> db:DB l -> t1:Term l
  -> t2:Term l
  -> { ε l (eval (ε l (Pg lc db (TBind t1 t2)))) = ε l (eval (Pg lc db (TBind t1 t2))) } 
@-}
simulationsBind 
  :: Label l => l -> l -> DB l -> Term l -> Term l -> Proof
simulationsBind l lc m t1 t2  = () 

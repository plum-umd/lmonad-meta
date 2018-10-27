{-@ LIQUID "--reflection"        @-}module Simulations.TUnlabel where

import ProofCombinators
import Labels 
import Programs 

import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsTUnlabel 
  :: Label l 
  => l:l
  -> lc:{l | canFlowTo lc l } 
  -> db:DB l -> t:Term l  
  -> { ε l (eval (ε l (Pg lc db (TUnlabel t)))) = ε l (eval (Pg lc db (TUnlabel t))) } 
@-}
simulationsTUnlabel :: Label l => l -> l -> DB l -> Term l -> Proof

simulationsTUnlabel l lc m t = undefined  

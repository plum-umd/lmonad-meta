{-@ LIQUID "--reflection"  @-}

module Simulations.TToLabeled where

import ProofCombinators
import Labels 
import Programs 
import Predicates 

import Idempotence 
import Simulations.Terms 
import Simulations.TToLabeledTVLabel

import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsTToLabeled  
  :: Label l => l:l 
  -> lc:l
  -> db:DB l 
  -> t1:Term l  
  -> t2:{Term l | terminates (Pg lc db (TToLabeled t1 t2))}
  -> {v:() | ε l (evalStar (ε l (Pg lc db t2))) == ε l (evalStar (Pg lc db t2)) }
  -> { ε l (eval (ε l (Pg lc db (TToLabeled t1 t2)))) == ε l (eval (Pg lc db (TToLabeled t1 t2))) } 
  @-}
simulationsTToLabeled :: (Label l, Eq l) 
  => l -> l -> DB l -> Term l -> Term l -> Proof -> Proof
simulationsTToLabeled l lc db t1 t2 simulationsStarP
  | lc `canFlowTo` l
  = simulationsTToLabeledFlows l lc db t1 t2 simulationsStarP
  | otherwise 
  = simulationsTToLabeledNotFlows l lc db t1 t2 simulationsStarP


{-@ simulationsTToLabeledNotFlows  
  :: Label l => l:l 
  -> lc:{l | not (canFlowTo lc l)}
  -> db:DB l 
  -> t1:Term l  
  -> t2:{Term l | terminates (Pg lc db (TToLabeled t1 t2))}
  -> {v:() | ε l (evalStar (ε l (Pg lc db t2))) == ε l (evalStar (Pg lc db t2)) }
  -> { ε l (eval (ε l (Pg lc db (TToLabeled t1 t2)))) == ε l (eval (Pg lc db (TToLabeled t1 t2))) } 
  @-}
simulationsTToLabeledNotFlows :: (Label l, Eq l) 
  => l -> l -> DB l -> Term l -> Term l -> Proof -> Proof

simulationsTToLabeledNotFlows l lc db t1@(TVLabel ll) t2 simulationsStarP
  = simulationsTToLabeledNotFlowsTVLabel l lc db ll t2 simulationsStarP

simulationsTToLabeledNotFlows l lc db t1 t2 _
  =   ε l (eval (ε l (Pg lc db (TToLabeled t1 t2)))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db)) 
  ==. PgHole (εDB l (εDB l db)) 
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
  ==. ε l (Pg lc db (TToLabeled (evalTerm t1) t2))
  ==. ε l (eval (Pg lc db (TToLabeled t1 t2)))
  *** QED 


{-@ simulationsTToLabeledNotFlowsTVLabel  
  :: Label l => l:l 
  -> lc:{l | not (canFlowTo lc l)}
  -> db:DB l 
  -> ll: l  
  -> t2:{Term l | terminates (Pg lc db (TToLabeled (TVLabel ll) t2))}
  -> {v:() | ε l (evalStar (ε l (Pg lc db t2))) == ε l (evalStar (Pg lc db t2)) }
  -> { ε l (eval (ε l (Pg lc db (TToLabeled (TVLabel ll) t2)))) == ε l (eval (Pg lc db (TToLabeled (TVLabel ll) t2))) } 
  @-}
simulationsTToLabeledNotFlowsTVLabel :: (Label l, Eq l) 
  => l -> l -> DB l -> l -> Term l -> Proof -> Proof
simulationsTToLabeledNotFlowsTVLabel l lc db ll t2 simulationsStarP
  | not (lc `canFlowTo` ll)
  =   ε l (eval (ε l (Pg lc db (TToLabeled t1 t2)))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db)) 
  ==. PgHole (εDB l (εDB l db)) 
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
  ==. ε l (Pg lc db (TLIO TException))
  ==. ε l (eval (Pg lc db (TToLabeled t1 t2)))
  *** QED 
  where t1 = TVLabel ll

simulationsTToLabeledNotFlowsTVLabel l lc db ll t2 simulationsStarP
  | Pg lc' db' (TLIO t') <- evalStar (Pg lc db t2)
  , lc' `canFlowTo` ll && lc `canFlowTo` ll
  =   ε l (eval (ε l (Pg lc db (TToLabeled t1 t2)))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db)) 
  ==. PgHole (εDB l (εDB l db)) 
  ==. ε l (PgHole (εDB l db)) 
  ==. ε l (evalStar (PgHole (εDB l db))) 
  ==. ε l (evalStar (ε l (Pg lc db t2))) 
      ? simulationsStarP
  ==. ε l (evalStar (Pg lc db t2))
  ==. ε l (Pg lc' db' (TLIO t'))
      ? lawFlowTransitivity lc lc' l
  ==. PgHole (εDB l db')
  ==. ε l (Pg lc db' (TLIO (TLabeled ll t')))
  ==. ε l (eval (Pg lc db (TToLabeled (TVLabel ll) t2)))
  *** QED 
  where t1 = TVLabel ll

simulationsTToLabeledNotFlowsTVLabel l lc db ll t2 simulationsStarP
  | Pg lc' db' t' <- evalStar (Pg lc db t2)
  =   ε l (eval (ε l (Pg lc db (TToLabeled t1 t2)))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db)) 
  ==. PgHole (εDB l (εDB l db)) 
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db) 
  ==. ε l (evalStar (PgHole (εDB l db))) 
  ==. ε l (evalStar (ε l (Pg lc db t2))) 
      ? simulationsStarP
  ==. ε l (evalStar (Pg lc db t2))
  ==. ε l (Pg lc' db' t')
      ? lawFlowTransitivity lc lc' l
  ==. PgHole (εDB l db')
  ==. ε l (Pg lc db' (TLIO (TLabeled ll TException)))
  ==. ε l (eval (Pg lc db (TToLabeled t1 t2)))
  *** QED 
  where t1 = TVLabel ll


{-@ simulationsTToLabeledFlows  
  :: Label l => l:l 
  -> lc:{l | canFlowTo lc l }
  -> db:DB l 
  -> t1:Term l  
  -> t2:{Term l | terminates (Pg lc db (TToLabeled t1 t2)) }
  -> { v:() | ε l (evalStar (ε l (Pg lc db t2))) == ε l (evalStar (Pg lc db t2)) }
  -> { ε l (eval (ε l (Pg lc db (TToLabeled t1 t2)))) == ε l (eval (Pg lc db (TToLabeled t1 t2))) } 
  @-}
simulationsTToLabeledFlows :: (Label l, Eq l) 
  => l -> l -> DB l -> Term l -> Term l -> Proof -> Proof

simulationsTToLabeledFlows l lc db (TVLabel ll) t2 simulationsStarP
  = simulationsTToLabeledTVLabel l lc db ll t2 simulationsStarP

simulationsTToLabeledFlows l lc db t1 t2 _ 
  =   ε l (eval (ε l (Pg lc db (TToLabeled t1 t2)))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TToLabeled t1 t2)))) 
  ==. ε l (eval (Pg lc (εDB l db) (TToLabeled (εTerm l t1) (εTerm l t2)))) 
  ==. ε l (Pg lc (εDB l db) (TToLabeled (evalTerm (εTerm l t1)) (εTerm l t2))) 
  ==. Pg lc (εDB l (εDB l db)) (εTerm l (TToLabeled (evalTerm (εTerm l t1)) (εTerm l t2)))
      ? εDBIdempotent l db 
      ? εTermIdempotent l t2 
      ? simulationsTerm l t1
  ==. Pg lc (εDB l db) (εTerm l (TToLabeled (evalTerm t1) t2))
  ==. ε l (Pg lc db (TToLabeled (evalTerm t1) t2))
  ==. ε l (eval (Pg lc db (TToLabeled t1 t2)))
  *** QED 

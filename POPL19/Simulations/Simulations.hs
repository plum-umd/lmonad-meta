{-@ LIQUID "--reflection"  @-}

module Simulations.Simulations where

import ProofCombinators
import Labels 
import Programs

import Idempotence 
import SafeErase 
import Simulations.Terms 
import Simulations.TUnlabel 
import Simulations.TBind 
import Simulations.TInsert 
import qualified Simulations.TInsertPgHole as IPgHole
import Simulations.TDelete 
import qualified Simulations.TDeletePgHole as DPgHole
import Simulations.TToLabeled 
import Simulations.Pure 
import Simulations.TUpdate 
import Simulations.TSelect 
import Monotonicity 
import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulations 
  :: Label l => l:l 
  -> p:{Program l | terminates p && ς p } 
  -> { ε l (eval (ε l p)) == ε l (eval p) } 
  / [evalSteps p, 0] @-}
simulations :: (Label l, Eq l) => l -> Program l -> Proof
simulations l (PgHole db)
  =   ε l (eval (ε l (PgHole db)))
  ==. ε l (eval (PgHole (εDB l db)))  
  ==. ε l (PgHole (εDB l db))  
  ==. PgHole (εDB l (εDB l db))  
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)  
  ==. ε l (PgHole db)  
  ==. ε l (eval (PgHole db))  
  *** QED 
 
simulations l (Pg lc db (TToLabeled t1 t2))
  = simulationsTToLabeled l lc db t1 t2 
      (evalStepsToLabeledAxiom lc db t1 t2 `cast` simulationsStar l (Pg lc db t2))

simulations l (Pg lc db (TDelete n t))
  = if lc `canFlowTo` l 
      then simulationsTDelete l lc db n t
      else DPgHole.simulationsTDelete l lc db n t

simulations l (Pg lc db (TInsert n t1 t2))
  = if lc `canFlowTo` l 
      then simulationsTInsert l lc db n t1 t2 
      else IPgHole.simulationsTInsert l lc db n t1 t2 

simulations l (Pg lc db (TUpdate n t1 t2 t3))
  = simulationsTUpdate l lc db n t1 t2 t3

simulations l (Pg lc db (TSelect n t))
  = simulationsTSelect l lc db n t  

simulations l (Pg lc db (TBind t1 t2))
  = undefined -- simulationsBind l lc db t1 t2 

simulations l (Pg lc db (TUnlabel t))
  = undefined -- simulationsTUnlabel l lc db t 

simulations l (Pg lc db (TReturn t))
  | lc `canFlowTo` l 
  =   ε l (eval (ε l (Pg lc db (TReturn t))))
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TReturn t))))
  ==. ε l (eval (Pg lc (εDB l db) (TReturn (εTerm l t))))
  ==. ε l (Pg lc (εDB l db) (TLIO (εTerm l t)))
  ==. Pg lc (εDB l (εDB l db)) (εTerm l (TLIO (εTerm l t)))
  ==. Pg lc (εDB l (εDB l db)) (TLIO (εTerm l (εTerm l t)))
      ? εTermIdempotent l t &&& εDBIdempotent l db 
  ==. Pg lc (εDB l db) (TLIO (εTerm l t))  
  ==. Pg lc (εDB l db) (εTerm l (TLIO t))  
  ==. ε l (Pg lc db (TLIO t))  
  ==. ε l (eval (Pg lc db (TReturn t)))  
  *** QED    
  | otherwise  
  =   ε l (eval (ε l (Pg lc db (TReturn t))))
  ==. ε l (eval (PgHole (εDB l db)))
  ==. ε l (PgHole (εDB l db))
  ==. PgHole (εDB l (εDB l db)) 
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
  ==. ε l (PgHole db )  
  ==. ε l (eval (Pg lc db (TReturn t)))  
  *** QED    

simulations l (Pg lc db t@(TLIO _))
  | lc `canFlowTo` l 
  =   ε l (eval (ε l (Pg lc db t)))
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l t)))
  ==. ε l (Pg lc (εDB l db) (evalTerm (εTerm l t)))
  ==. Pg lc (εDB l (εDB l db)) (εTerm l (evalTerm (εTerm l t)))
      ? simulationsTerm l t &&& εDBIdempotent l db 
  ==. Pg lc (εDB l db) (εTerm l (evalTerm t))  
  ==. ε l (Pg lc db (evalTerm t))  
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
  ==. ε l (eval (Pg lc db t))  
  *** QED    

simulations l (Pg lc db t)
  | isPure t 
  = simulationsPure l lc db t 


{-@ simulationsStar 
  :: Label l => l:l 
  -> p:{Program l | terminates p && ς p } 
  -> { ε l (evalStar (ε l p)) == ε l (evalStar p) } 
  / [evalSteps p, 1] @-}
simulationsStar :: (Label l, Eq l) => l -> Program l -> Proof
simulationsStar l (PgHole db) 
  =   ε l (evalStar (ε l (PgHole db))) 
  ==. ε l (evalStar (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db)) 
  ==. PgHole (εDB l (εDB l db)) 
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db) 
  ==. ε l (PgHole db) 
  ==. ε l (evalStar (PgHole db)) 
  *** QED 

simulationsStar l p@(Pg lc db t) 
  | isValue t, lc `canFlowTo` l 
  =   ε l (evalStar (ε l (Pg lc db t))) 
  ==. ε l (evalStar (Pg lc (εDB l db) (εTerm l t)))
  ==. ε l (Pg lc (εDB l db) (εTerm l t))
      ? εDBIdempotent   l db 
      ? εTermIdempotent l t  
  ==. ε l (Pg lc db t) 
  ==. ε l (evalStar (Pg lc db t)) 
  *** QED 

  | isValue t
  =   ε l (evalStar (ε l (Pg lc db t))) 
  ==. ε l (evalStar (PgHole (εDB l db)))
  ==. ε l (PgHole (εDB l db))
      ? εDBIdempotent l db 
  ==. ε l (Pg lc db t) 
  ==. ε l (evalStar (Pg lc db t)) 
  *** QED 

  | otherwise 
  =   ε l (evalStar p) 
  ==. ε l (evalStar (eval p))
      ? evalStepsAxiom p
      ? simulationsStar l (eval p)
  ==. ε l (evalStar (ε l (eval p)))
      ? evalStepsAxiom p
      ? simulations l p
      ? safeErase l (eval (ε l p))
  ==. ε l (evalStar (ε l (eval (ε l p))))
      ? evalStepsAxiom p
      ? evalStepsAxiomErase l p 
      ? safeErase l p
      ? simulationsStar l (eval (ε l p))
  ==. ε l (evalStar (eval (ε l p)))
      ? assert (not (isValue (εTerm l t)))
  ==. ε l (evalStar (ε l p)) 
  *** QED 

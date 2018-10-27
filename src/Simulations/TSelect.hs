{-@ LIQUID "--reflection"  @-}

module Simulations.TSelect (simulationsTSelect) where

import ProofCombinators
import Labels 
import Programs 

import Idempotence 
import LookupTableErase 
import LabelSelectTable 
import LabelSelectErase 
import Simulations.Terms 
import Simulations.Select

import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsTSelect  
  :: Label l => l:l 
  -> lc:l
  -> db:DB l 
  -> n:TName 
  -> t:{Term l | terminates (Pg lc db (TSelect n t))}
  -> { ε l (eval (ε l (Pg lc db (TSelect n t)))) == ε l (eval (Pg lc db (TSelect n t))) } 
  @-}
simulationsTSelect :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Term l -> Proof

simulationsTSelect l lc db n p 
  | lc `canFlowTo` l 
  = simulationsFlows l lc db n p  
  | otherwise 
  = simulationsDoesNotFlow l lc db n p 


{-@ simulationsFlows  
  :: Label l => l:l 
  -> lc:{l | canFlowTo lc l }
  -> db:DB l 
  -> n:TName 
  -> t:{Term l | terminates (Pg lc db (TSelect n t))}
  -> { ε l (eval (ε l (Pg lc db (TSelect n t)))) == ε l (eval (Pg lc db (TSelect n t))) } 
  @-}
simulationsFlows :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Term l -> Proof

simulationsFlows l lc db n (TPred p) 
  | Just ti <- lookupTable n db 
  =   lookupTableErase l n db 
  &&& simulationsTSelectFound l lc db n p ti 

simulationsFlows l lc db n (TPred p) 
  | Just ti <- lookupTable n (εDB l db)
  = assert (isJust (lookupTable n (εDB l db)))
  ? assert (not (isJust (lookupTable n db)))
  ? lookupTableErase l n db
  ? assert False 

simulationsFlows l lc db n (TPred p) 
  =   ε l (eval (ε l (Pg lc db (TSelect n (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TSelect n (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TSelect n (εTerm l (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TSelect n (TPred p)))) 
  ==. ε l (Pg lc (εDB l db) TException) 
  ==. Pg lc (εDB l (εDB l db)) (εTerm l TException)
      ? εDBIdempotent l db  
  ==. Pg lc (εDB l db) (εTerm l TException)
  ==. ε l (Pg lc db TException)
  ==. ε l (eval (Pg lc db (TSelect n (TPred p))))
  *** QED 

simulationsFlows l lc db n t 
  =   ε l (eval (ε l (Pg lc db (TSelect n t)))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TSelect n t)))) 
  ==. ε l (eval (Pg lc (εDB l db) (TSelect n (εTerm l t)))) 
  ==. ε l (Pg lc (εDB l db) (TSelect n (evalTerm (εTerm l t)))) 
  ==. Pg lc (εDB l (εDB l db)) (εTerm l (TSelect n (evalTerm (εTerm l t)))) 
  ==. Pg lc (εDB l (εDB l db)) (TSelect n (εTerm l (evalTerm (εTerm l t))))
       ? simulationsTerm l t &&& εDBIdempotent l db  
  ==. Pg lc (εDB l db) (TSelect n (εTerm l (evalTerm t))) 
  ==. Pg lc (εDB l db) (εTerm l (TSelect n (evalTerm t))) 
  ==. ε l (Pg lc db (TSelect n (evalTerm t))) 
  ==. ε l (eval (Pg lc db (TSelect n t))) 
  *** QED 

{-@ simulationsTSelectFound  
  :: Label l => l:l 
  -> lc:{l | canFlowTo lc l }
  -> db:DB l 
  -> n:TName 
  -> p:{Pred | terminates (Pg lc db (TSelect n (TPred p)))}
  -> t:{Table l | (isJust (lookupTable n (εDB l db))) && (isJust (lookupTable n db))
                }
  -> { ε l (eval (ε l (Pg lc db (TSelect n (TPred p))))) == ε l (eval (Pg lc db (TSelect n (TPred p)))) } 
  @-}
simulationsTSelectFound :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> Table l -> Proof

simulationsTSelectFound l lc db n p _ 
  =   ε l (eval (ε l (Pg lc db (TSelect n (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TSelect n (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TSelect n (εTerm l (TPred p))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TSelect n (TPred p)))) 
  ==. ε l (Pg εlc' (εDB l db) (TReturn (selectDB (εDB l db) n p))) 
      ? joinCanFlowTo lc (labelSelectTable p εti) l  
  ==. ( if labelSelectTable p εti `canFlowTo` l 
          then Pg εlc' (εDB l (εDB l db)) (εTerm l (TReturn (selectDB (εDB l db) n p)))
          else PgHole (εDB l (εDB l db)))
      ? εDBIdempotent l db
  ==. ( if labelSelectTable p εti `canFlowTo` l 
          then Pg εlc' (εDB l db) (TReturn (εTerm l (selectDB (εDB l db) n p)))
               ? labelSelectTableImplies l p εti 
               ? labelSelectErase l p n db
               ? simulationsSelect l db n p ti
          else PgHole (εDB l db))
      ? assert (ti  == fromJust (lookupTable n db))
      ? assert (εti == fromJust (lookupTable n (εDB l db)))
  ==. ( if labelSelectTable p εti `canFlowTo` l 
          then Pg lc' (εDB l db) (TReturn (εTerm l (selectDB db n p)))
          else PgHole (εDB l db))
      ? labelSelectEraseIff l p n db 
  ==. ( if labelSelectTable p ti `canFlowTo` l 
          then Pg lc' (εDB l db) (TReturn (εTerm l (selectDB db n p)))
          else PgHole (εDB l db))
  ==. ( if labelSelectTable p ti `canFlowTo` l 
          then Pg lc' (εDB l db) (εTerm l (TReturn (selectDB db n p)))
          else PgHole (εDB l db))
      ? joinCanFlowTo lc (labelSelectTable p ti) l  
  ==. ε l (Pg lc' db (TReturn (selectDB db n p))) 
  ==. ε l (eval (Pg lc db (TSelect n (TPred p)))) 
  *** QED 
  where 
    lc'  = lc `join` labelSelectTable p ti
    εlc' = lc `join` labelSelectTable p εti
    ti   = case lookupTable n db of Just t -> t
    εti  = case lookupTable n (εDB l db) of Just t -> t 


{-@ simulationsDoesNotFlow  
  :: Label l => l:l 
  -> lc:{l | not (canFlowTo lc l) }
  -> db:DB l 
  -> n:TName 
  -> t:{Term l | terminates (Pg lc db (TSelect n t))}
  -> { ε l (eval (ε l (Pg lc db (TSelect n t)))) == ε l (eval (Pg lc db (TSelect n t))) } 
  @-}
simulationsDoesNotFlow :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Term l -> Proof

simulationsDoesNotFlow l lc db n (TPred p) 
  | Just ti <- lookupTable n db 
  =   ε l (eval (ε l (Pg lc db (TSelect n (TPred p))))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db)) 
  ==. PgHole (εDB l (εDB l db))
      ? εDBIdempotent l db  
  ==. PgHole (εDB l db)
      ? joinCanFlowTo lc (labelSelectTable p ti) l 
  ==. ε l (Pg (lc `join` labelSelectTable p ti) db (TReturn (selectDB db n p)))
  ==. ε l (eval (Pg lc db (TSelect n (TPred p))))
  *** QED 

simulationsDoesNotFlow l lc db n (TPred p) 
  =   ε l (eval (ε l (Pg lc db (TSelect n (TPred p))))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db)) 
  ==. PgHole (εDB l (εDB l db)) 
      ? εDBIdempotent l db  
  ==. PgHole (εDB l db) 
  ==. ε l (Pg lc db TException)
  ==. ε l (eval (Pg lc db (TSelect n (TPred p))))
  *** QED 

simulationsDoesNotFlow l lc db n t 
  =   ε l (eval (ε l (Pg lc db (TSelect n t)))) 
  ==. ε l (eval (PgHole (εDB l db))) 
  ==. ε l (PgHole (εDB l db)) 
  ==. PgHole (εDB l (εDB l db))  
      ? εDBIdempotent l db  
  ==. PgHole (εDB l db)
  ==. ε l (Pg lc db (TSelect n (evalTerm t))) 
  ==. ε l (eval (Pg lc db (TSelect n t))) 
  *** QED 


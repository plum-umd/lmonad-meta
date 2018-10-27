{-@ LIQUID "--reflection"  @-}

module Simulations.TToLabeledTVLabel where

import ProofCombinators
import Labels 
import Programs 

import Idempotence 
import Simulations.Terms 

import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsTToLabeledTVLabel  
  :: Label l => l:l 
  -> lc:{l | canFlowTo lc l }
  -> db:DB l 
  -> ll: l  
  -> t2:{Term l | terminates (Pg lc db (TToLabeled (TVLabel ll) t2))}
  -> { v:() | ε l (evalStar (ε l (Pg lc db t2))) == ε l (evalStar (Pg lc db t2)) }
  -> { ε l (eval (ε l (Pg lc db (TToLabeled (TVLabel ll) t2)))) == ε l (eval (Pg lc db (TToLabeled (TVLabel ll) t2))) } 
  @-}
simulationsTToLabeledTVLabel :: (Label l, Eq l) 
  => l -> l -> DB l -> l -> Term l -> Proof -> Proof

simulationsTToLabeledTVLabel l lc db ll t2 _
  | not (lc `canFlowTo` ll)
  =   ε l (eval (ε l (Pg lc db (TToLabeled (TVLabel ll) t2)))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TToLabeled (TVLabel ll) t2)))) 
  ==. ε l (eval (Pg lc (εDB l db) (TToLabeled (εTerm l (TVLabel ll)) (εTerm l t2)))) 
  ==. ε l (eval (Pg lc (εDB l db) (TToLabeled (TVLabel ll) (εTerm l t2)))) 
  ==. ε l (Pg lc (εDB l db) (TLIO TException)) 
  ==. Pg lc (εDB l (εDB l db)) (εTerm l (TLIO TException)) 
      ? εDBIdempotent l db
  ==. Pg lc (εDB l db) (εTerm l (TLIO TException)) 
  ==. ε l (Pg lc db  (TLIO TException))
  ==. ε l (eval (Pg lc db (TToLabeled (TVLabel ll) t2)))
  *** QED 
  | (ll `canFlowTo` l)  
  =   ε l (eval (ε l (Pg lc db (TToLabeled (TVLabel ll) t2)))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TToLabeled (TVLabel ll) t2)))) 
  ==. ε l (eval (Pg lc (εDB l db) (TToLabeled (εTerm l (TVLabel ll)) (εTerm l t2)))) 
  ==. ε l (eval (Pg lc (εDB l db) (TToLabeled (TVLabel ll) (εTerm l t2)))) 
  ==. ε l (Pg lc εdb' (TLIO (TLabeled ll (if (εb && εc) then fromTLIO εmt' else TException))))
  ==. Pg lc (εDB l εdb') (εTerm l (TLIO (TLabeled ll (if (εb && εc) then fromTLIO εmt' else TException))))
      ? globals
      ? (if b && εb && lc' `canFlowTo` l then  
        (    εTerm l (TLIO (TLabeled ll (fromTLIO εmt')))
         ==. TLIO (εTerm l (TLabeled ll (fromTLIO εmt'))) 
         ==. TLIO (TLabeled ll (εTerm l (fromTLIO εmt'))) 
         ==. TLIO (TLabeled ll (εTerm l (fromTLIO mt')))
         ==. TLIO (εTerm l (TLabeled ll (fromTLIO mt')))
         ==. εTerm l (TLIO (TLabeled ll (fromTLIO mt')))
         *** QED) else ())
      -- ? if not (εb && εc) I need simulations on db!
      ? assert (εDB l db'  == εDB l εdb')
      ? assert (if (lc' `canFlowTo` l) then εTerm l mt' == εTerm l εmt' else True)
  ==. Pg lc (εDB l db') (εTerm l (TLIO (TLabeled ll (if b && c then fromTLIO mt' else TException))))
  ==. ε l (Pg lc db' (TLIO (TLabeled ll (if b && c then fromTLIO mt' else TException)))) 
  ==. ε l (eval (Pg lc db (TToLabeled (TVLabel ll) t2)))
  *** QED 

  | otherwise 
  =   ε l (eval (ε l (Pg lc db (TToLabeled (TVLabel ll) t2)))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TToLabeled (TVLabel ll) t2)))) 
  ==. ε l (eval (Pg lc (εDB l db) (TToLabeled (εTerm l (TVLabel ll)) (εTerm l t2)))) 
  ==. ε l (eval (Pg lc (εDB l db) (TToLabeled (TVLabel ll) (εTerm l t2)))) 
  ==. ε l (Pg lc εdb' (TLIO (TLabeled ll (if (εb && εc) then fromTLIO εmt' else TException))))
  ==. Pg lc (εDB l εdb') (εTerm l (TLIO (TLabeled ll (if (εb && εc) then fromTLIO εmt' else TException))))
  ==. Pg lc (εDB l εdb') (TLIO (εTerm l (TLabeled ll (if (εb && εc) then fromTLIO εmt' else TException))))
  ==. Pg lc (εDB l εdb') (TLIO (TLabeled ll THole))
      ? globals
      ? assert (εDB l db'  == εDB l εdb')
  ==. Pg lc (εDB l db') (TLIO (TLabeled ll THole))
  ==. Pg lc (εDB l db') (TLIO (εTerm l (TLabeled ll (if b && c then fromTLIO mt' else TException))))
  ==. Pg lc (εDB l db') (εTerm l (TLIO (TLabeled ll (if b && c then fromTLIO mt' else TException))))
  ==. ε l (Pg lc db' (TLIO (TLabeled ll (if b && c then fromTLIO mt' else TException)))) 
  ==. ε l (eval (Pg lc db (TToLabeled (TVLabel ll) t2)))
  *** QED 

  where
    Pg lc'  db'  mt'  = evalStar (Pg lc db t2)
    Pg εlc' εdb' εmt' = evalStar (Pg lc (εDB l db) (εTerm l t2))

    a  = lc   `canFlowTo` ll
    z  = lc'  `canFlowTo` l
    εz = εlc' `canFlowTo` l

    b  = isTLIO mt'
    εb = isTLIO εmt'

    c  = lc'  `canFlowTo` ll
    εc = εlc' `canFlowTo` ll

    globals  = 
          (if εlc' `canFlowTo` l then Pg εlc' (εDB l εdb') (εTerm l εmt') 
                                 else PgHole  (εDB l εdb'))
      ==. ε l (Pg εlc' εdb' εmt') 
      ==. ε l (evalStar (Pg lc (εDB l db) (εTerm l t2))) 
      ==. ε l (evalStar (ε l (Pg lc db t2))) 
      ==. ε l (evalStar (Pg lc db t2))
      ==. ε l (Pg lc' db' mt')
      ==. (if lc' `canFlowTo` l then Pg lc' (εDB l db') (εTerm l mt') else PgHole (εDB l db'))
      *** QED   
      `const` assert (εDB l db' == εDB l εdb')         
      -- `const` assert (z `iff` εz)         
      -- `const` assert (z `impl` (εlc' == lc'))         
      -- `const` assert (z `impl` (εTerm l εmt' == εTerm l mt'))
      -- `const` assert (z `impl` (b == εb))
      `const` (lawFlowTransitivity lc   ll l) 
      `const` (lawFlowTransitivity lc'  ll l) 
      `const` (lawFlowTransitivity εlc' ll l) 
      `const` case mt'  of {TLIO t' -> assert b  ; _ -> ()}
      `const` case εmt' of {TLIO t' -> assert εb ; _ -> ()}

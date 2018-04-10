{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}
{-@ LIQUID "--max-case-expand=0"                        @-}

module Simulations.TBind where

import Label
import Language
import Programs 
import MetaFunctions 
import Simulations.Language
import Simulations.MetaFunctions
import Simulations.Programs
import Simulations.Helpers
import Simulations.EraseEvalErase
import Termination

import ProofCombinators

{-@ simulationsTBind :: l:Label -> lc:{Label | canFlowTo lc l} -> c:Label -> m:Memory -> t1:Term -> t2:{Term | terminates (Pg lc c m (TBind t1 t2)) } 
 -> {v : Proof | ε l (evalProgram (Pg lc c m (TBind (εTerm l t1) (εTerm l t2)))) == ε l (evalProgram (Pg lc c m (TBind t1 t2))) }
 @-}

simulationsTBind :: Label -> Label -> Label -> Memory -> Term -> Term -> Proof 

simulationsTBind l lc c m t1 t2 
  | l'' `canFlowTo` l, l' `canFlowTo` l 
  =   ε l (evalProgram (Pg lc c m (TBind (εTerm l t1) (εTerm l t2))))
  ==. ε l (Pg l' c' m' (TApp (εTerm l t2) t')) 
  ==. Pg l' c' m' (εTerm l (TApp (εTerm l t2) t')) 
  ==. Pg l' c' m' (TApp (εTerm l (εTerm l t2)) (εTerm l t')) 
  ==. Pg l' c' m' (TApp (εTerm l t2) (εTerm l t')) ? εTermIdempotent l t2  
  ==. Pg l' c' m' (TApp (εTerm l t2) (εTerm l t')) ? 
        (     Pg l' c' m' (εTerm l t')
          ==. ε l (Pg l' c' m' t')
          ==. ε l (evalProgramStar (Pg lc c m (εTerm l t1)))
          ==. ε l (evalProgramStar (ε l (Pg lc c m t1)))
          ==. ε l (evalProgramStar (Pg lc c m t1)) 
              ? terminationAxiomTBind lc c m t1 t2 &&& simulationsStar'' (Pg lc c m t1) l 
          ==. ε l (Pg l'' c'' m'' t'')
          ==. Pg l'' c'' m'' (εTerm l t'')
          *** QED 
        )
  ==. Pg l'' c'' m'' (TApp (εTerm l t2) (εTerm l t''))
  ==. Pg l'' c'' m'' (εTerm l (TApp t2 t''))
  ==. ε l (Pg l'' c'' m'' (TApp t2 t''))
  ==. ε l (evalProgram (Pg lc c m (TBind t1 t2)))
  *** QED 
  | not (l'' `canFlowTo` l), not (l' `canFlowTo` l) 
  =   ε l (evalProgram (Pg lc c m (TBind (εTerm l t1) (εTerm l t2))))
  ==. ε l (Pg l' c' m' (TApp (εTerm l t2) t')) 
  ==. PgHole 
  ==. ε l (Pg l'' c'' m'' (TApp t2 t''))
  ==. ε l (evalProgram (Pg lc c m (TBind t1 t2)))
  *** QED 
  | not (l'' `canFlowTo` l),  l' `canFlowTo` l
  =   Pg l' c' m' (εTerm l t')
  ==. ε l (Pg l' c' m' t')
  ==. ε l (evalProgramStar (Pg lc c m (εTerm l t1)))
  ==. ε l (evalProgramStar (ε l (Pg lc c m t1)))
  ==. ε l (evalProgramStar (Pg lc c m t1)) 
      ? terminationAxiomTBind lc c m t1 t2 &&& simulationsStar'' (Pg lc c m t1) l 
  ==. ε l (Pg l'' c'' m'' t'')
  ==. PgHole
  *** QED 
  | l'' `canFlowTo` l, not (l' `canFlowTo` l)
  =   PgHole
  ==. ε l (Pg l' c' m' t')
  ==. ε l (evalProgramStar (Pg lc c m (εTerm l t1)))
  ==. ε l (evalProgramStar (ε l (Pg lc c m t1)))
  ==. ε l (evalProgramStar (Pg lc c m t1)) 
      ? terminationAxiomTBind lc c m t1 t2 &&& simulationsStar'' (Pg lc c m t1) l 
  ==. ε l (Pg l'' c'' m'' t'')
  ==. Pg l'' c'' m'' (εTerm l t'')
  *** QED 
   where
    Pg l' c' m' t'     = evalProgramStar (Pg lc c m (εTerm l t1))
    Pg l'' c'' m'' t'' = evalProgramStar (Pg lc c m t1)


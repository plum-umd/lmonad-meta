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

{-@ simulationsTBind :: l:Label -> lc:{Label | canFlowTo lc l} -> c:Label -> m:Memory -> t1:Term -> t2:Term 
 -> {v : Proof | ε l (evalProgram (ε l (Pg lc c m (TBind t1 t2)))) == ε l (evalProgram (Pg lc c m (TBind t1 t2)))}
 / [size t1] @-}

simulationsTBind :: Label -> Label -> Label -> Memory -> Term -> Term -> Proof 
simulationsTBind l lc c m THole t2  
  =   ε l (evalProgram (ε l (Pg lc c m (TBind THole t2))))
  ==. ε l (evalProgram (Pg lc c m (εTerm l (TBind THole t2))))
  ==. ε l (evalProgram (Pg lc c m (TBind (εTerm l THole) (εTerm l t2))))
  ==. ε l (evalProgram (Pg lc c m (TBind THole (εTerm l t2) )))
      ? (evalProgramStar (Pg lc c m THole) ==. (Pg lc c m THole) *** QED)
  ==. ε l (Pg lc c m (TApp (εTerm l t2) THole))
  ==. Pg lc c m (εTerm l (TApp (εTerm l t2) THole))
  ==. Pg lc c m (TApp (εTerm l (εTerm l t2)) (εTerm l THole))
      ? εTermIdempotent l t2
  ==. Pg lc c m (TApp (εTerm l t2) (εTerm l THole)) 
  ==. Pg lc c m (εTerm l (TApp t2 THole)) 
  ==. ε l (Pg lc c m (TApp t2 THole)) 
      ?   (evalProgramStar (Pg lc c m THole) ==. (Pg lc c m THole) *** QED)
      &&& (isValue THole *** QED )
  ==. ε l (evalProgram (Pg lc c m (TBind THole t2))) 
  *** QED 


simulationsTBind l lc c m t1 t2 = 
  undefined  




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
 -> {v : Proof | ε l (evalProgram (Pg lc c m (TBind (εTerm l t1) (εTerm l t2)))) == ε l (evalProgram (Pg lc c m (TBind t1 t2))) }
 @-}

simulationsTBind :: Label -> Label -> Label -> Memory -> Term -> Term -> Proof 
simulationsTBind l lc c m t1 t2 | isValue t1, isValue (εTerm l t1)
  =   ε l (evalProgram (Pg lc c m (TBind (εTerm l t1) (εTerm l t2))))
  ==. ε l (Pg lc c m (TApp (εTerm l t2) (εTerm l t1)))
      ? (evalProgramStar (Pg lc c m (εTerm l t1)) ==. Pg lc c m (εTerm l t1) *** QED)
  ==. Pg lc c m (εTerm l (TApp (εTerm l t2) (εTerm l t1)))
  ==. Pg lc c m (TApp (εTerm l (εTerm l t2)) (εTerm l (εTerm l t1)))
  ==. Pg lc c m (TApp (εTerm l t2) (εTerm l t1))
      ? εTermIdempotent l t1 &&& εTermIdempotent l t2 
  ==. Pg lc c m (εTerm l (TApp t2 t1))
  ==. ε l (Pg lc c m (TApp t2 t1))
  ==. ε l (evalProgram (Pg lc c m (TBind t1 t2)))
     ? (evalProgramStar (Pg lc c m t1) ==. Pg lc c m t1 *** QED)
  *** QED 


simulationsTBind l lc c m TGetLabel t2
  =   ε l (evalProgram (Pg lc c m (TBind (εTerm l TGetLabel) (εTerm l t2))))
  ==. ε l (evalProgram (Pg lc c m (TBind TGetLabel (εTerm l t2))))
  ==. ε l (Pg lc c m (TApp (εTerm l t2) (TVLabel lc)))
      ? (   evalProgramStar (Pg lc c m TGetLabel)
        ==. evalProgramStar (evalProgram (Pg lc c m TGetLabel))
        ==. evalProgramStar (Pg lc c m (TVLabel lc))  ? (isValue (TVLabel lc) *** QED)
        ==. Pg lc c m (TVLabel lc)
        *** QED )
  ==. Pg lc c m (εTerm l (TApp (εTerm l t2) (TVLabel lc)))
  ==. Pg lc c m (TApp (εTerm l (εTerm l t2)) (εTerm l (TVLabel lc)))
      ? εTermIdempotent l t2 
  ==. Pg lc c m (TApp (εTerm l t2) (εTerm l (TVLabel lc)))
  ==. Pg lc c m (εTerm l (TApp t2 (TVLabel lc)))
  ==. ε l (Pg lc c m (TApp t2 (TVLabel c)))
  ==. ε l (evalProgram (Pg lc c m (TBind TGetLabel t2)))
  *** QED 

simulationsTBind l lc c m TGetClearance t2
  =   ε l (evalProgram (Pg lc c m (TBind (εTerm l TGetClearance) (εTerm l t2))))
  ==. ε l (evalProgram (Pg lc c m (TBind TGetClearance (εTerm l t2))))
  ==. ε l (Pg lc c m (TApp (εTerm l t2) (TVLabel c)))
      ? (   evalProgramStar (Pg lc c m TGetClearance)
        ==. evalProgramStar (evalProgram (Pg lc c m TGetClearance))
        ==. evalProgramStar (Pg lc c m (TVLabel c))  ? (isValue (TVLabel c) *** QED)
        ==. Pg lc c m (TVLabel c)
        *** QED )
  ==. Pg lc c m (εTerm l (TApp (εTerm l t2) (TVLabel c)))
  ==. Pg lc c m (TApp (εTerm l (εTerm l t2)) (εTerm l (TVLabel c)))
      ? εTermIdempotent l t2 
  ==. Pg lc c m (TApp (εTerm l t2) (εTerm l (TVLabel c)))
  ==. Pg lc c m (εTerm l (TApp t2 (TVLabel c)))
  ==. ε l (Pg lc c m (TApp t2 (TVLabel c)))
  ==. ε l (evalProgram (Pg lc c m (TBind TGetClearance t2)))
  *** QED 

simulationsTBind l lc c m (TBind t11 t12) t2
  =   ε l (evalProgram (Pg lc c m (TBind (εTerm l (TBind t11 t12)) (εTerm l t2))))
  -- HERE 
  ==? ε l (evalProgram (Pg lc c m (TBind (TBind t11 t12) t2)))
  ==. ε l (evalProgram (Pg lc c m (TBind (TBind t11 t12) t2)))
  *** QED 

simulationsTBind l lc c m t1 t2
  = undefined 

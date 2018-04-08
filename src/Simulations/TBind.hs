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
simulationsTBind l lc c m (TLam v t1') t2 
  =   ε l (evalProgram (ε l (Pg lc c m (TBind (TLam v t1') t2))))
  ==. ε l (evalProgram (Pg lc c m (εTerm l (TBind (TLam v t1') t2))))
  ==. ε l (evalProgram (Pg lc c m (TBind (εTerm l (TLam v t1')) (εTerm l t2))))
  ==. ε l (evalProgram (Pg lc c m (TBind (TLam v (εTerm l t1')) (εTerm l t2) )))
      ? (evalProgramStar (Pg lc c m (TLam v (εTerm l t1'))) ==. Pg lc c m (TLam v (εTerm l t1')) *** QED)
  ==. ε l (Pg lc c m (TApp (εTerm l t2) (TLam v (εTerm l t1'))))
  ==. Pg lc c m (εTerm l (TApp (εTerm l t2) (TLam v (εTerm l t1'))))
  ==. Pg lc c m (TApp (εTerm l (εTerm l t2)) (εTerm l (TLam v (εTerm l t1'))))
  ==. Pg lc c m (TApp (εTerm l (εTerm l t2)) (TLam v (εTerm l (εTerm l t1'))))
      ? εTermIdempotent l t2 &&& εTermIdempotent l t1' 
  ==. Pg lc c m (TApp (εTerm l t2) (TLam v (εTerm l t1'))) 
  ==. Pg lc c m (TApp (εTerm l t2) (εTerm l (TLam v t1'))) 
  ==. Pg lc c m (εTerm l (TApp t2 (TLam v t1'))) 
  ==. ε l (Pg lc c m (TApp t2 (TLam v t1'))) 
      ?   (evalProgramStar (Pg lc c m (TLam v t1')) ==. (Pg lc c m (TLam v t1')) *** QED)
      &&& (isValue (TLam v t1') *** QED)
  ==. ε l (evalProgram (Pg lc c m (TBind (TLam v t1') t2))) 
  *** QED 

simulationsTBind l lc c m (TVLabel l') t2  
  =   ε l (evalProgram (ε l (Pg lc c m (TBind (TVLabel l') t2))))
  ==. ε l (evalProgram (Pg lc c m (εTerm l (TBind (TVLabel l') t2))))
  ==. ε l (evalProgram (Pg lc c m (TBind (εTerm l (TVLabel l')) (εTerm l t2))))
  ==. ε l (evalProgram (Pg lc c m (TBind (TVLabel l') (εTerm l t2))))
      ? (evalProgramStar (Pg lc c m ((TVLabel l'))) ==. Pg lc c m (TVLabel l') *** QED)
  ==. ε l (Pg lc c m (TApp (εTerm l t2) (TVLabel l')))
  ==. Pg lc c m (εTerm l (TApp (εTerm l t2) (TVLabel l')))
  ==. Pg lc c m (TApp (εTerm l (εTerm l t2)) (εTerm l (TVLabel l')))
  ==. Pg lc c m (TApp (εTerm l (εTerm l t2)) (TVLabel l'))
      ? εTermIdempotent l t2 
  ==. Pg lc c m (TApp (εTerm l t2) (TVLabel l')) 
  ==. Pg lc c m (TApp (εTerm l t2) (εTerm l (TVLabel l'))) 
  ==. Pg lc c m (εTerm l (TApp t2 (TVLabel l'))) 
  ==. ε l (Pg lc c m (TApp t2 (TVLabel l'))) 
      ? (evalProgramStar (Pg lc c m (TVLabel l')) ==. (Pg lc c m (TVLabel l')) *** QED)
      &&& (isValue (TVLabel l') *** QED)
  ==. ε l (evalProgram (Pg lc c m (TBind (TVLabel l') t2))) 
  *** QED 

simulationsTBind l lc c m t1 t2  | TLabeledTCB _ _ <- t1 
  = undefined 

simulationsTBind l lc c m TUnit t2 
  =   ε l (evalProgram (ε l (Pg lc c m (TBind TUnit t2))))
  ==. ε l (evalProgram (Pg lc c m (εTerm l (TBind TUnit t2))))
  ==. ε l (evalProgram (Pg lc c m (TBind (εTerm l TUnit) (εTerm l t2))))
  ==. ε l (evalProgram (Pg lc c m (TBind TUnit (εTerm l t2) )))
      ? (evalProgramStar (Pg lc c m TUnit) ==. (Pg lc c m TUnit) *** QED)
  ==. ε l (Pg lc c m (TApp (εTerm l t2) TUnit))
  ==. Pg lc c m (εTerm l (TApp (εTerm l t2) TUnit))
  ==. Pg lc c m (TApp (εTerm l (εTerm l t2)) (εTerm l TUnit))
      ? εTermIdempotent l t2
  ==. Pg lc c m (TApp (εTerm l t2) (εTerm l TUnit)) 
  ==. Pg lc c m (εTerm l (TApp t2 TUnit)) 
  ==. ε l (Pg lc c m (TApp t2 TUnit)) 
      ?   (evalProgramStar (Pg lc c m TUnit) ==. (Pg lc c m TUnit) *** QED)
  ==. ε l (evalProgram (Pg lc c m (TBind TUnit t2))) 
  *** QED 


simulationsTBind l lc c m TTrue t2 
  =   ε l (evalProgram (ε l (Pg lc c m (TBind TTrue t2))))
  ==. ε l (evalProgram (Pg lc c m (εTerm l (TBind TTrue t2))))
  ==. ε l (evalProgram (Pg lc c m (TBind (εTerm l TTrue) (εTerm l t2))))
  ==. ε l (evalProgram (Pg lc c m (TBind TTrue (εTerm l t2) )))
      ? (evalProgramStar (Pg lc c m TTrue) ==. (Pg lc c m TTrue) *** QED)
  ==. ε l (Pg lc c m (TApp (εTerm l t2) TTrue))
  ==. Pg lc c m (εTerm l (TApp (εTerm l t2) TTrue))
  ==. Pg lc c m (TApp (εTerm l (εTerm l t2)) (εTerm l TTrue))
      ? εTermIdempotent l t2
  ==. Pg lc c m (TApp (εTerm l t2) (εTerm l TTrue)) 
  ==. Pg lc c m (εTerm l (TApp t2 TTrue)) 
  ==. ε l (Pg lc c m (TApp t2 TTrue)) 
      ?   (evalProgramStar (Pg lc c m TTrue) ==. (Pg lc c m TTrue) *** QED)
  ==. ε l (evalProgram (Pg lc c m (TBind TTrue t2))) 
  *** QED 


simulationsTBind l lc c m TFalse t2 
  =   ε l (evalProgram (ε l (Pg lc c m (TBind TFalse t2))))
  ==. ε l (evalProgram (Pg lc c m (εTerm l (TBind TFalse t2))))
  ==. ε l (evalProgram (Pg lc c m (TBind (εTerm l TFalse) (εTerm l t2))))
  ==. ε l (evalProgram (Pg lc c m (TBind TFalse (εTerm l t2) )))
      ? (evalProgramStar (Pg lc c m TFalse) ==. (Pg lc c m TFalse) *** QED)
  ==. ε l (Pg lc c m (TApp (εTerm l t2) TFalse))
  ==. Pg lc c m (εTerm l (TApp (εTerm l t2) TFalse))
  ==. Pg lc c m (TApp (εTerm l (εTerm l t2)) (εTerm l TFalse))
      ? εTermIdempotent l t2
  ==. Pg lc c m (TApp (εTerm l t2) (εTerm l TFalse)) 
  ==. Pg lc c m (εTerm l (TApp t2 TFalse)) 
  ==. ε l (Pg lc c m (TApp t2 TFalse)) 
      ?   (evalProgramStar (Pg lc c m TFalse) ==. (Pg lc c m TFalse) *** QED)
  ==. ε l (evalProgram (Pg lc c m (TBind TFalse t2))) 
  *** QED 

simulationsTBind l lc c m TException t2 
  =   ε l (evalProgram (ε l (Pg lc c m (TBind TException t2))))
  ==. ε l (evalProgram (Pg lc c m (εTerm l (TBind TException t2))))
  ==. ε l (evalProgram (Pg lc c m (TBind (εTerm l TException) (εTerm l t2))))
  ==. ε l (evalProgram (Pg lc c m (TBind TException (εTerm l t2) )))
      ? (evalProgramStar (Pg lc c m TException) ==. (Pg lc c m TException) *** QED)
  ==. ε l (Pg lc c m (TApp (εTerm l t2) TException))
  ==. Pg lc c m (εTerm l (TApp (εTerm l t2) TException))
  ==. Pg lc c m (TApp (εTerm l (εTerm l t2)) (εTerm l TException))
      ? εTermIdempotent l t2
  ==. Pg lc c m (TApp (εTerm l t2) (εTerm l TException)) 
  ==. Pg lc c m (εTerm l (TApp t2 TException)) 
  ==. ε l (Pg lc c m (TApp t2 TException)) 
      ?   (evalProgramStar (Pg lc c m TException) ==. (Pg lc c m TException) *** QED)
  ==. ε l (evalProgram (Pg lc c m (TBind TException t2))) 
  *** QED 

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
  ==. ε l (evalProgram (Pg lc c m (TBind THole t2))) 
  *** QED   


simulationsTBind l lc c m (TVar x) t2  
  =   ε l (evalProgram (ε l (Pg lc c m (TBind (TVar x) t2))))
  ==. ε l (evalProgram (Pg lc c m (εTerm l (TBind (TVar x) t2))))
  ==. ε l (evalProgram (Pg lc c m (TBind (εTerm l (TVar x)) (εTerm l t2))))
  ==. ε l (evalProgram (Pg lc c m (TBind (TVar x) (εTerm l t2))))
      ?   (assumeValueVar x)
      &&& (evalProgramStar (Pg lc c m (TVar x)) ==. (Pg lc c m (TVar x)) *** QED)
  ==. ε l (Pg lc c m (TApp (εTerm l t2) (TVar x)))
  ==. Pg lc c m (εTerm l (TApp (εTerm l t2) (TVar x)))
  ==. Pg lc c m (TApp (εTerm l (εTerm l t2)) (εTerm l (TVar x)))
      ? εTermIdempotent l t2
  ==. Pg lc c m (TApp (εTerm l t2) (εTerm l (TVar x))) 
  ==. Pg lc c m (εTerm l (TApp t2 (TVar x))) 
  ==. ε l (Pg lc c m (TApp t2 (TVar x))) 
      ?   (evalProgramStar (Pg lc c m (TVar x)) ==. (Pg lc c m (TVar x)) *** QED)
  ==. ε l (evalProgram (Pg lc c m (TBind (TVar x) t2))) 
  *** QED   


simulationsTBind l lc c m (TApp t1' t2') t2  
  = undefined 

simulationsTBind l lc c m (TFix t1') t2  
  = undefined 

simulationsTBind l lc c m (TIf t1' t2' t3') t2  
  = undefined 

simulationsTBind l lc c m (TJoin t1' t2') t2  
  = undefined 

simulationsTBind l lc c m (TMeet t1' t2') t2  
  = undefined 

simulationsTBind l lc c m (TCanFlowTo t1' t2') t2  
  = undefined 

simulationsTBind l lc c m (TBind t1' t2') t2  
  = undefined 

simulationsTBind l lc c m TGetLabel t2  
  = undefined 

simulationsTBind l lc c m TGetClearance t2  
  = undefined 

simulationsTBind l lc c m (TLowerClearance t1') t2  
  = undefined 

simulationsTBind l lc c m (TLabeledTCB l' t1') t2  
  = undefined 

simulationsTBind l lc c m (TLabelOf t1') t2  
  = undefined 

simulationsTBind l lc c m (TLabel t1' t2') t2  
  = undefined 

simulationsTBind l lc c m (TUnlabel t1') t2  
  = undefined 

simulationsTBind l lc c m (TToLabeled t1' t2') t2  
  = undefined 



-- NV: IF not (isValue (TVar x)), THEN evalProgramStar diverges on Var
{-@ assumeValueVar :: x:Var -> {isValue (TVar x)} @-}
assumeValueVar :: Var -> Proof 
assumeValueVar = undefined 

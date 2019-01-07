{-@ LIQUID "--reflection" @-}

module Simulations.Terms where

import ProofCombinators
import Programs
import Labels 
import Idempotence 
import HomomorphicSubst 
import Prelude hiding (Maybe(..), fromJust, isJust)



{-@ simulationsTerm 
  :: (Eq l, Label l) => l:l
  -> t:Term l
  -> { εTerm l (evalTerm (εTerm l t)) = εTerm l (evalTerm t) }
@-}
simulationsTerm :: (Eq l, Label l) => l -> Term l -> Proof
 
simulationsTerm l t@TException 
  =   εTerm l (evalTerm (εTerm l t)) 
  ==. εTerm l (evalTerm t) 
  *** QED 
simulationsTerm l t@THole 
  =   εTerm l (evalTerm (εTerm l t)) 
  ==. εTerm l (evalTerm t) 
  *** QED 
simulationsTerm l t@TUnit 
  =   εTerm l (evalTerm (εTerm l t)) 
  ==. εTerm l (evalTerm t) 
  *** QED 
simulationsTerm l t@TNil 
  =   εTerm l (evalTerm (εTerm l t)) 
  ==. εTerm l (evalTerm t) 
  *** QED 
simulationsTerm l (TCons h t) 
  =   εTerm l (evalTerm (εTerm l (TCons h t))) 
  ==. εTerm l (evalTerm (TCons (εTerm l h) (εTerm l t))) 
  ==. εTerm l (TCons (εTerm l h) (εTerm l t)) 
  ==. TCons (εTerm l (εTerm l h)) (εTerm l (εTerm l t)) 
       ? εTermIdempotent l h &&& εTermIdempotent l t 
  ==. TCons (εTerm l h) (εTerm l t) 
  ==. εTerm l (TCons h t) 
  ==. εTerm l (evalTerm (TCons h t)) 
  *** QED 

simulationsTerm l t@TNothing 
  =   εTerm l (evalTerm (εTerm l t)) 
  ==. εTerm l (evalTerm t) 
  *** QED 

simulationsTerm l t@(TInt _) 
  =   εTerm l (evalTerm (εTerm l t)) 
  ==. εTerm l (evalTerm t) 
  *** QED 
simulationsTerm l t@(TPred _) 
  =   εTerm l (evalTerm (εTerm l t)) 
  ==. εTerm l (evalTerm t) 
  *** QED 
simulationsTerm l (TLabeled l1 t) 
  | l1 `canFlowTo` l 
  =   εTerm l (evalTerm (εTerm l (TLabeled l1 t))) 
  ==. εTerm l (evalTerm (TLabeled l1 (εTerm l t))) 
  ==. εTerm l (TLabeled l1 (εTerm l t)) 
  ==. TLabeled l1 (εTerm l (εTerm l t)) 
      ? εTermIdempotent l t 
  ==. TLabeled l1 (εTerm l t) 
  ==. εTerm l (TLabeled l1 t) 
  ==. εTerm l (evalTerm (TLabeled l1 t)) 
  *** QED 

simulationsTerm l (TLabeled l1 t) 
  =   εTerm l (evalTerm (εTerm l (TLabeled l1 t))) 
  ==. εTerm l (evalTerm (TLabeled l1 THole)) 
  ==. εTerm l (TLabeled l1 THole) 
  ==. TLabeled l1 THole 
  ==. εTerm l (TLabeled l1 t) 
  ==. εTerm l (evalTerm (TLabeled l1 t)) 
  *** QED 



simulationsTerm l (TInsert n t1 t2) 
  =   εTerm l (evalTerm (εTerm l (TInsert n t1 t2))) 
  ==. εTerm l (evalTerm (TInsert n (εTerm l t1) (εTerm l t2))) 
  ==. εTerm l (TInsert n (εTerm l t1) (εTerm l t2)) 
  ==. TInsert n (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2)) 
       ? εTermIdempotent l t1 &&& εTermIdempotent l t2
  ==. TInsert n (εTerm l t1) (εTerm l t2)
  ==. εTerm l (TInsert n t1 t2) 
  ==. εTerm l (evalTerm (TInsert n t1 t2))
  *** QED 

simulationsTerm l (TSelect n t) 
  =   εTerm l (evalTerm (εTerm l (TSelect n t))) 
  ==. εTerm l (evalTerm (TSelect n (εTerm l t))) 
  ==. εTerm l (TSelect n (εTerm l t)) 
  ==. TSelect n (εTerm l (εTerm l t)) 
       ? εTermIdempotent l t 
  ==. TSelect n (εTerm l t) 
  ==. εTerm l (TSelect n t) 
  ==. εTerm l (evalTerm (TSelect n t)) 
  *** QED 

simulationsTerm l (TDelete n t) 
  =   εTerm l (evalTerm (εTerm l (TDelete n t))) 
  ==. εTerm l (evalTerm (TDelete n (εTerm l t))) 
  ==. εTerm l (TDelete n (εTerm l t)) 
  ==. TDelete n (εTerm l (εTerm l t)) 
       ? εTermIdempotent l t 
  ==. TDelete n (εTerm l t) 
  ==. εTerm l (TDelete n t) 
  ==. εTerm l (evalTerm (TDelete n t)) 
  *** QED   

simulationsTerm l (TUpdate n t1 t2 t3) 
  =   εTerm l (evalTerm (εTerm l (TUpdate n t1 t2 t3))) 
  ==. εTerm l (evalTerm (TUpdate n (εTerm l t1) (εTerm l t2) (εTerm l t3))) 
  ==. εTerm l (TUpdate n (εTerm l t1) (εTerm l t2) (εTerm l t3)) 
  ==. TUpdate n (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2)) (εTerm l (εTerm l t3))
       ? εTermIdempotent l t1 &&& εTermIdempotent l t2 &&& εTermIdempotent l t3
  ==. TUpdate n (εTerm l t1) (εTerm l t2) (εTerm l t3) 
  ==. εTerm l (TUpdate n t1 t2 t3) 
  ==. εTerm l (evalTerm (TUpdate n t1 t2 t3)) 
  *** QED  


simulationsTerm l t@TTrue
  =   εTerm l (evalTerm (εTerm l t)) 
  ==. εTerm l (evalTerm t) 
  *** QED 

simulationsTerm l t@TFalse
  =   εTerm l (evalTerm (εTerm l t)) 
  ==. εTerm l (evalTerm t) 
  *** QED   

simulationsTerm l t@(TVLabel _)
  =   εTerm l (evalTerm (εTerm l t)) 
  ==. εTerm l (evalTerm t) 
  *** QED 
  
simulationsTerm l t@(TVar _)
  =   εTerm l (evalTerm (εTerm l t)) 
  ==. εTerm l (evalTerm t) 
  *** QED  

simulationsTerm l (TLam x t)
  =   εTerm l (evalTerm (εTerm l (TLam x t))) 
  ==. εTerm l (evalTerm (TLam x (εTerm l t))) 
  ==. εTerm l (TLam x (εTerm l t)) 
  ==. εTerm l (εTerm l (TLam x t))
       ? εTermIdempotent l (TLam x t) 
  ==. εTerm l (TLam x t) 
  ==. εTerm l (evalTerm (TLam x t)) 
  *** QED 

simulationsTerm l (TLIO t)
  =   εTerm l (evalTerm (εTerm l (TLIO t))) 
  ==. εTerm l (evalTerm (TLIO (εTerm l t))) 
  ==. εTerm l (TLIO (εTerm l t)) 
  ==. εTerm l (εTerm l (TLIO t))
      ? εTermIdempotent l (TLIO t) 
  ==. εTerm l (TLIO t) 
  ==. εTerm l (evalTerm (TLIO t)) 
  *** QED

simulationsTerm l (TReturn t)
  =   εTerm l (evalTerm (εTerm l (TReturn t))) 
  ==. εTerm l (evalTerm (TReturn (εTerm l t))) 
  ==. εTerm l (TReturn (εTerm l t)) 
  ==. εTerm l (εTerm l (TReturn t))
      ? εTermIdempotent l (TReturn t) 
  ==. εTerm l (TReturn t) 
  ==. εTerm l (evalTerm (TReturn t)) 
  *** QED

simulationsTerm l t@(TToLabeled t1 t2)
  =   εTerm l (evalTerm (εTerm l (TToLabeled t1 t2))) 
  ==. εTerm l (evalTerm (TToLabeled (εTerm l t1) (εTerm l t))) 
  ==. εTerm l (TToLabeled (εTerm l t1) (εTerm l t)) 
  ==. TToLabeled (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2))
       ? εTermIdempotent l t1 &&& εTermIdempotent l t2 
  ==. TToLabeled (εTerm l t1) (εTerm l t2) 
  ==. εTerm l (TToLabeled t1 t2) 
  ==. εTerm l (evalTerm (TToLabeled t1 t2)) 
  *** QED   

simulationsTerm l t@(TBind t1 t2)
  =   εTerm l (evalTerm (εTerm l (TBind t1 t2))) 
  ==. εTerm l (evalTerm (TBind (εTerm l t1) (εTerm l t))) 
  ==. εTerm l (TBind (εTerm l t1) (εTerm l t)) 
  ==. TBind (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2))
       ? εTermIdempotent l t1 &&& εTermIdempotent l t2 
  ==. TBind (εTerm l t1) (εTerm l t2) 
  ==. εTerm l (TBind t1 t2) 
  ==. εTerm l (evalTerm (TBind t1 t2)) 
  *** QED  

simulationsTerm l (TUnlabel t)
  =   εTerm l (evalTerm (εTerm l (TUnlabel t))) 
  ==. εTerm l (evalTerm (TUnlabel (εTerm l t))) 
  ==. εTerm l (TUnlabel (εTerm l t)) 
  ==. TUnlabel (εTerm l (εTerm l t)) 
  ==. TUnlabel (εTerm l t) ? εTermIdempotent l t 
  ==. εTerm l (TUnlabel t) 
  ==. εTerm l (evalTerm (TUnlabel t)) 
  *** QED 

simulationsTerm l (TIf TTrue t1 t2)
  =   εTerm l (evalTerm (εTerm l (TIf TTrue t1 t2))) 
  ==. εTerm l (evalTerm (TIf (εTerm l TTrue) (εTerm l t1) (εTerm l t2))) 
  ==. εTerm l (evalTerm (TIf TTrue (εTerm l t1) (εTerm l t2))) 
  ==. εTerm l (εTerm l t1)
      ? εTermIdempotent l t1
  ==. εTerm l t1
  ==. εTerm l (evalTerm (TIf TTrue t1 t2)) 
  *** QED     

simulationsTerm l (TIf TFalse t1 t2)
  =   εTerm l (evalTerm (εTerm l (TIf TFalse t1 t2))) 
  ==. εTerm l (evalTerm (TIf (εTerm l TFalse) (εTerm l t1) (εTerm l t2))) 
  ==. εTerm l (evalTerm (TIf TFalse (εTerm l t1) (εTerm l t2))) 
  ==. εTerm l (εTerm l t2)
      ? εTermIdempotent l t2
  ==. εTerm l t2
  ==. εTerm l (evalTerm (TIf TFalse t1 t2)) 
  *** QED     

simulationsTerm l (TIf THole t1 t2)
  =   εTerm l (evalTerm (εTerm l (TIf THole t1 t2))) 
  ==. εTerm l (evalTerm (TIf (εTerm l THole) (εTerm l t1) (εTerm l t2))) 
  ==. εTerm l (evalTerm (TIf THole (εTerm l t1) (εTerm l t2))) 
  ==. εTerm l (εTerm l t1)
      ? εTermIdempotent l t1
  ==. εTerm l THole
  ==. εTerm l (evalTerm (TIf THole t1 t2)) 
  *** QED     


simulationsTerm l (TIf t t1 t2)
  =   εTerm l (evalTerm (εTerm l (TIf t t1 t2))) 
  ==. εTerm l (evalTerm (TIf (εTerm l t) (εTerm l t1) (εTerm l t2))) 
  ==. εTerm l (TIf (evalTerm (εTerm l t)) (εTerm l t1) (εTerm l t2)) 
  ==. TIf (εTerm l (evalTerm (εTerm l t))) (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2))
      ? εTermIdempotent l t1 
      ? εTermIdempotent l t2 
      ? simulationsTerm l t  
  ==. TIf (εTerm l (evalTerm t)) (εTerm l t1) (εTerm l t2) 
  ==. εTerm l (TIf (evalTerm t) t1 t2) 
  ==. εTerm l (evalTerm (TIf t t1 t2)) 
  *** QED     


simulationsTerm l (TJust t)
  =   εTerm l (evalTerm (εTerm l (TJust t)))
  ==. εTerm l (evalTerm (TJust (εTerm l t)))
  ==. εTerm l (TJust (εTerm l t))
  ==. TJust (εTerm l (εTerm l t))
      ? εTermIdempotent l t
  ==. TJust (εTerm l t)
  ==. εTerm l (TJust t) 
  ==. εTerm l (evalTerm (TJust t))       
  *** QED


simulationsTerm l (TCase TNothing t1 t2)
  =   εTerm l (evalTerm (εTerm l (TCase TNothing t1 t2)))
  ==. εTerm l (evalTerm (TCase (εTerm l TNothing) (εTerm l t1) (εTerm l t2)))
  ==. εTerm l (evalTerm (TCase TNothing (εTerm l t1) (εTerm l t2)))
  ==. εTerm l (εTerm l t2)
      ? εTermIdempotent l t2
  ==. εTerm l t2
  ==. εTerm l (evalTerm (TCase TNothing t1 t2))
  *** QED

simulationsTerm l (TCase (TJust a) t1 t2)
  =   εTerm l (evalTerm (εTerm l (TCase (TJust a) t1 t2)))
  ==. εTerm l (evalTerm (TCase (εTerm l (TJust a)) (εTerm l t1) (εTerm l t2)))
  ==. εTerm l (evalTerm (TCase (TJust (εTerm l a)) (εTerm l t1) (εTerm l t2)))
  ==. εTerm l (evalTerm (TApp (εTerm l t1) (εTerm l a)))
  ==. εTerm l (evalTerm (εTerm l (TApp t1 a)))
  ==. εTerm l (evalTerm (TApp t1 a))
      ? simulationsTerm l (TApp t1 a)
  ==. εTerm l (evalTerm (TCase (TJust a) t1 t2))
  *** QED



simulationsTerm l (TCase THole t1 t2)
  =   εTerm l (evalTerm (εTerm l (TCase THole t1 t2))) 
  ==. εTerm l (evalTerm (TCase (εTerm l THole) (εTerm l t1) (εTerm l t2))) 
  ==. εTerm l (evalTerm (TCase THole (εTerm l t1) (εTerm l t2))) 
  ==. εTerm l THole
  ==. εTerm l (evalTerm (TCase THole t1 t2)) 
  *** QED     


simulationsTerm l (TCase t t1 t2)
  =   εTerm l (evalTerm (εTerm l (TCase t t1 t2))) 
  ==. εTerm l (evalTerm (TCase (εTerm l t) (εTerm l t1) (εTerm l t2))) 
  ==. εTerm l (TCase (evalTerm (εTerm l t)) (εTerm l t1) (εTerm l t2)) 
  ==. TCase (εTerm l (evalTerm (εTerm l t))) (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2))
  ==. TCase (evalTerm (εTerm l (εTerm l t))) (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2))
      ? εTermIdempotent l t1 
      ? εTermIdempotent l t2 
      ? simulationsTerm l t
  ==. TCase (εTerm l (evalTerm t)) (εTerm l t1) (εTerm l t2) 
  ==. εTerm l (TCase (evalTerm t) t1 t2) 
  ==. εTerm l (evalTerm (TCase t t1 t2)) 
  *** QED


simulationsTerm l (TApp (TLam x t1) t2) 
  =   εTerm l (evalTerm (εTerm l (TApp (TLam x t1) t2))) 
  ==. εTerm l (evalTerm (TApp (εTerm l (TLam x t1)) (εTerm l t2))) 
  ==. εTerm l (evalTerm (TApp (TLam x (εTerm l t1)) (εTerm l t2))) 
  ==. εTerm l (subst x (εTerm l t2) (εTerm l t1)) 
  ==. εTerm l (εTerm l (subst x t2 t1)) 
       ? homomorphicSubst l x t2 t1 
  ==. εTerm l (subst x t2 t1)
       ? εTermIdempotent l (subst x t2 t1)
  ==. εTerm l (evalTerm (TApp (TLam x t1) t2)) 
  *** QED    


simulationsTerm l (TApp t1 t2)
  =   εTerm l (evalTerm (εTerm l (TApp t1 t2))) 
  ==. εTerm l (evalTerm (TApp (εTerm l t1) (εTerm l t2))) 
  ==. εTerm l (TApp (evalTerm (εTerm l t1)) (εTerm l t2)) 
  ==. TApp (εTerm l (evalTerm (εTerm l t1))) (εTerm l (εTerm l t2))
      ? εTermIdempotent l t2 
      ? simulationsTerm l t1  
  ==. TApp (εTerm l (evalTerm t1)) (εTerm l t2) 
  ==. εTerm l (TApp (evalTerm t1) t2) 
  ==. εTerm l (evalTerm (TApp t1 t2)) 
  *** QED     


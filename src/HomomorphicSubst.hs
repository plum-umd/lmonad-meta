{-@ LIQUID "--reflection" @-}

module HomomorphicSubst where

import Prelude hiding (Maybe(..), fromJust, isJust)

import ProofCombinators
import Programs
 
import Labels 
import Idempotence 


homomorphicSubst :: (Label l, Eq l) => l -> Var -> Term l -> Term l -> Proof 
{-@ homomorphicSubst :: Label l => l:l -> x:Var -> tx:Term l -> t:Term l
  ->  { εTerm l (subst x tx t) == subst x (εTerm l tx) (εTerm l t) } / [tsize t, 1] @-}
homomorphicSubst l x tx t@(TVar y) 
  | x == y 
  =   subst x (εTerm l tx) (εTerm l t) 
  ==. subst x (εTerm l tx) t
  ==. εTerm l tx
  ==. εTerm l (subst x tx t)
  *** QED 
  | otherwise
  =   subst x (εTerm l tx) (εTerm l t) 
  ==. εTerm l t
  ==. εTerm l (subst x tx t)
  *** QED 


homomorphicSubst l x tx t@(TLam y ty) 
  | x == y 
  =   subst x (εTerm l tx) (εTerm l (TLam y ty)) 
  ==. subst x (εTerm l tx) (TLam y (εTerm l ty)) 
  ==. TLam y (εTerm l ty) 
  ==. εTerm l (TLam y  ty) 
  ==. εTerm l (subst x tx t)
  *** QED 
  | otherwise
  =   subst x (εTerm l tx) (εTerm l (TLam y ty)) 
  ==. subst x (εTerm l tx) (TLam y (εTerm l ty)) 
  ==. TLam y (subst x (εTerm l tx)  (εTerm l ty)) 
      ? homomorphicSubst l x tx ty
  ==. TLam y (εTerm l (subst x tx ty)) 
  ==. εTerm l (subst x tx (TLam y ty))
  *** QED 

homomorphicSubst l x tx (TApp t1 t2)
  =   subst x (εTerm l tx) (εTerm l (TApp t1 t2)) 
  ==. subst x (εTerm l tx) (TApp (εTerm l t1) (εTerm l t2)) 
  ==. TApp (subst x (εTerm l tx) (εTerm l t1)) (subst x (εTerm l tx) (εTerm l t2)) 
      ? homomorphicSubst l x tx t1 
      ? homomorphicSubst l x tx t2
  ==. TApp (εTerm l (subst x tx t1)) (εTerm l (subst x tx t2)) 
  ==. εTerm l (subst x tx (TApp t1 t2))
  *** QED 

homomorphicSubst l x tx (TIf t1 t2 t3)
  =   subst x (εTerm l tx) (εTerm l (TIf t1 t2 t3)) 
  ==. subst x (εTerm l tx) (TIf (εTerm l t1) (εTerm l t2) (εTerm l t3)) 
  ==. TIf (subst x (εTerm l tx) (εTerm l t1))
          (subst x (εTerm l tx) (εTerm l t2)) 
          (subst x (εTerm l tx) (εTerm l t3)) 
      ? homomorphicSubst l x tx t1 
      ? homomorphicSubst l x tx t2
      ? homomorphicSubst l x tx t3
  ==. TIf (εTerm l (subst x tx t1)) (εTerm l (subst x tx t2)) (εTerm l (subst x tx t3))  
  ==. εTerm l (subst x tx (TIf t1 t2 t3))
  *** QED 

homomorphicSubst l x tx (TLIO t) 
  =   subst x (εTerm l tx) (εTerm l (TLIO t)) 
  ==. subst x (εTerm l tx) (TLIO (εTerm l t)) 
  ==. TLIO (subst x (εTerm l tx) (εTerm l t))
      ? homomorphicSubst l x tx t
  ==. TLIO (εTerm l (subst x tx t))
  ==. εTerm l (subst x tx (TLIO t))
  *** QED 

homomorphicSubst l x tx (TReturn t) 
  =   subst x (εTerm l tx) (εTerm l (TReturn t)) 
  ==. subst x (εTerm l tx) (TReturn (εTerm l t)) 
  ==. TReturn (subst x (εTerm l tx) (εTerm l t))
      ? homomorphicSubst l x tx t
  ==. TReturn (εTerm l (subst x tx t))
  ==. εTerm l (subst x tx (TReturn t))
  *** QED 

homomorphicSubst l x tx (TToLabeled t1 t2)
  =   subst x (εTerm l tx) (εTerm l (TToLabeled t1 t2)) 
  ==. subst x (εTerm l tx) (TToLabeled (εTerm l t1) (εTerm l t2)) 
  ==. TToLabeled (subst x (εTerm l tx) (εTerm l t1)) (subst x (εTerm l tx) (εTerm l t2)) 
      ? homomorphicSubst l x tx t1 
      ? homomorphicSubst l x tx t2
  ==. TToLabeled (εTerm l (subst x tx t1)) (εTerm l (subst x tx t2)) 
  ==. εTerm l (subst x tx (TToLabeled t1 t2))
  *** QED 

homomorphicSubst l x tx (TBind t1 t2)
  =   subst x (εTerm l tx) (εTerm l (TBind t1 t2)) 
  ==. subst x (εTerm l tx) (TBind (εTerm l t1) (εTerm l t2)) 
  ==. TBind (subst x (εTerm l tx) (εTerm l t1)) (subst x (εTerm l tx) (εTerm l t2)) 
      ? homomorphicSubst l x tx t1 
      ? homomorphicSubst l x tx t2
  ==. TBind (εTerm l (subst x tx t1)) (εTerm l (subst x tx t2)) 
  ==. εTerm l (subst x tx (TBind t1 t2))
  *** QED 

homomorphicSubst l x tx (TInsert n t1 t2)
  =   subst x (εTerm l tx) (εTerm l (TInsert n t1 t2)) 
  ==. subst x (εTerm l tx) (TInsert n (εTerm l t1) (εTerm l t2)) 
  ==. TInsert n (subst x (εTerm l tx) (εTerm l t1)) (subst x (εTerm l tx) (εTerm l t2)) 
      ? homomorphicSubst l x tx t1 
      ? homomorphicSubst l x tx t2
  ==. TInsert n (εTerm l (subst x tx t1)) (εTerm l (subst x tx t2)) 
  ==. εTerm l (subst x tx (TInsert n t1 t2))
  *** QED 

homomorphicSubst l x tx (TUpdate n t1 t2 t3)
  =   subst x (εTerm l tx) (εTerm l (TUpdate n t1 t2 t3)) 
  ==. subst x (εTerm l tx) (TUpdate n (εTerm l t1) (εTerm l t2) (εTerm l t3)) 
  ==. TUpdate n (subst x (εTerm l tx) (εTerm l t1)) 
                (subst x (εTerm l tx) (εTerm l t2)) 
                (subst x (εTerm l tx) (εTerm l t3)) 
      ? homomorphicSubst l x tx t1 
      ? homomorphicSubst l x tx t2
      ? homomorphicSubst l x tx t3
  ==. TUpdate n (εTerm l (subst x tx t1)) (εTerm l (subst x tx t2)) (εTerm l (subst x tx t3)) 
  ==. εTerm l (TUpdate n (subst x tx t1) (subst x tx t2) (subst x tx t3))
  ==. εTerm l (subst x tx (TUpdate n t1 t2 t3))
  *** QED 

homomorphicSubst l x tx (TSelect n t)
  =   subst x (εTerm l tx) (εTerm l (TSelect n t)) 
  ==. subst x (εTerm l tx) (TSelect n (εTerm l t)) 
  ==. TSelect n (subst x (εTerm l tx) (εTerm l t))
      ? homomorphicSubst l x tx t 
  ==. TSelect n (εTerm l (subst x tx t))  
  ==. εTerm l (subst x tx (TSelect n t))
  *** QED 

homomorphicSubst l x tx (TDelete n t)
  =   subst x (εTerm l tx) (εTerm l (TDelete n t)) 
  ==. subst x (εTerm l tx) (TDelete n (εTerm l t)) 
  ==. TDelete n (subst x (εTerm l tx) (εTerm l t))
      ? homomorphicSubst l x tx t 
  ==. TDelete n (εTerm l (subst x tx t))  
  ==. εTerm l (subst x tx (TDelete n t))
  *** QED 

homomorphicSubst l x tx (TUnlabel t)
  =   subst x (εTerm l tx) (εTerm l (TUnlabel t)) 
  ==. subst x (εTerm l tx) (TUnlabel (εTerm l t)) 
  ==. TUnlabel (subst x (εTerm l tx) (εTerm l t))
      ? homomorphicSubst l x tx t 
  ==. TUnlabel (εTerm l (subst x tx t))  
  ==. εTerm l (subst x tx (TUnlabel t))
  *** QED 


homomorphicSubst l x tx (TLabeled l1 t)
  | l1 `canFlowTo` l 
  =   subst x (εTerm l tx) (εTerm l (TLabeled l1 t)) 
  ==. subst x (εTerm l tx) (TLabeled l1 (εTerm l t)) 
  ==. TLabeled l1 (subst x (εTerm l tx) (εTerm l t))
      ? homomorphicSubst l x tx t 
  ==. TLabeled l1 (εTerm l (subst x tx t))  
  ==. εTerm l (subst x tx (TLabeled l1 t))
  *** QED 
  | otherwise
  =   subst x (εTerm l tx) (εTerm l (TLabeled l1 t)) 
  ==. subst x (εTerm l tx) (TLabeled l1 THole) 
  ==. TLabeled l1 (subst x (εTerm l tx) THole) 
  ==. TLabeled l1 THole
  ==. εTerm l (TLabeled l1 THole)
  ==. εTerm l (TLabeled l1 (subst x tx THole))
  ==. εTerm l (subst x tx (TLabeled l1 t))
  *** QED 

homomorphicSubst l x tx (TCons t1 t2)
  =   subst x (εTerm l tx) (εTerm l (TCons t1 t2)) 
  ==. subst x (εTerm l tx) (TCons (εTerm l t1) (εTerm l t2)) 
  ==. TCons (subst x (εTerm l tx) (εTerm l t1)) (subst x (εTerm l tx) (εTerm l t2)) 
      ? homomorphicSubst l x tx t1 
      ? homomorphicSubst l x tx t2
  ==. TCons (εTerm l (subst x tx t1)) (εTerm l (subst x tx t2)) 
  ==. εTerm l (subst x tx (TCons t1 t2))
  *** QED 

homomorphicSubst l x tx TNil 
  =   subst x (εTerm l tx) (εTerm l TNil) 
  ==. subst x (εTerm l tx) TNil 
  ==. TNil
  ==. εTerm l TNil
  ==. εTerm l (subst x tx TNil)
  *** QED 

homomorphicSubst l x tx (TPred p) 
  =   subst x (εTerm l tx) (εTerm l (TPred p)) 
  ==. subst x (εTerm l tx) (TPred p) 
  ==. (TPred p)
  ==. εTerm l (TPred p)
  ==. εTerm l (subst x tx (TPred p))
  *** QED 

homomorphicSubst l x tx TNothing 
  =   subst x (εTerm l tx) (εTerm l TNothing) 
  ==. subst x (εTerm l tx) TNothing 
  ==. TNothing
  ==. εTerm l TNothing
  ==. εTerm l (subst x tx TNothing)
  *** QED

homomorphicSubst l x tx (TJust t) 
  =   subst x (εTerm l tx) (εTerm l (TJust t)) 
  ==. subst x (εTerm l tx) (TJust (εTerm l t)) 
  ==. TJust (subst x (εTerm l tx) (εTerm l t))
      ? homomorphicSubst l x tx t
  ==. TJust (εTerm l (subst x tx t))
  ==. εTerm l (subst x tx (TJust t))
  *** QED   

homomorphicSubst l x tx (TCase t1 t2 t3)
  =   subst x (εTerm l tx) (εTerm l (TCase t1 t2 t3)) 
  ==. subst x (εTerm l tx) (TCase (εTerm l t1) (εTerm l t2) (εTerm l t3)) 
  ==. TCase (subst x (εTerm l tx) (εTerm l t1))
          (subst x (εTerm l tx) (εTerm l t2)) 
          (subst x (εTerm l tx) (εTerm l t3)) 
      ? homomorphicSubst l x tx t1 
      ? homomorphicSubst l x tx t2
      ? homomorphicSubst l x tx t3
  ==. TCase (εTerm l (subst x tx t1)) (εTerm l (subst x tx t2)) (εTerm l (subst x tx t3))  
  ==. εTerm l (subst x tx (TCase t1 t2 t3))
  *** QED 

homomorphicSubst l x tx THole 
  =   subst x (εTerm l tx) (εTerm l THole) 
  ==. subst x (εTerm l tx) THole 
  ==. THole
  ==. εTerm l THole
  ==. εTerm l (subst x tx THole)
  *** QED 

homomorphicSubst l x tx TException 
  =   subst x (εTerm l tx) (εTerm l TException) 
  ==. subst x (εTerm l tx) TException 
  ==. TException
  ==. εTerm l TException
  ==. εTerm l (subst x tx TException)
  *** QED     


homomorphicSubst l x tx TTrue 
  =   subst x (εTerm l tx) (εTerm l TTrue) 
  ==. subst x (εTerm l tx) TTrue 
  ==. TTrue
  ==. εTerm l TTrue
  ==. εTerm l (subst x tx TTrue)
  *** QED 


homomorphicSubst l x tx TFalse 
  =   subst x (εTerm l tx) (εTerm l TFalse) 
  ==. subst x (εTerm l tx) TFalse 
  ==. TFalse
  ==. εTerm l TFalse
  ==. εTerm l (subst x tx TFalse)
  *** QED 


homomorphicSubst l x tx TUnit 
  =   subst x (εTerm l tx) (εTerm l TUnit) 
  ==. subst x (εTerm l tx) TUnit 
  ==. TUnit
  ==. εTerm l TUnit
  ==. εTerm l (subst x tx TUnit)
  *** QED 


homomorphicSubst l x tx (TInt i) 
  =   subst x (εTerm l tx) (εTerm l (TInt i)) 
  ==. subst x (εTerm l tx) (TInt i) 
  ==. (TInt i)
  ==. εTerm l (TInt i)
  ==. εTerm l (subst x tx (TInt i))
  *** QED 


homomorphicSubst l x tx (TVLabel ll) 
  =   subst x (εTerm l tx) (εTerm l (TVLabel ll)) 
  ==. subst x (εTerm l tx) (TVLabel ll) 
  ==. (TVLabel ll)
  ==. εTerm l (TVLabel ll)
  ==. εTerm l (subst x tx (TVLabel ll))
  *** QED  

{- 
homomorphicSubstTInsert :: (Label l, Eq l) => l -> Var -> Term l -> TName -> Term l -> Term l -> Proof 
{-@ homomorphicSubstTInsert 
  :: Label l => l:l -> x:Var -> tx:Term l -> n:TName -> t1:Term l -> t2:Term l  
  ->  { εTerm l (subst x tx (TInsert n t1 t2)) == subst x (εTerm l tx) (εTerm l (TInsert n t1 t2)) } 
  / [(1 + tsize t1 + tsize t2), 0] @-}
homomorphicSubstTInsert l x tx n (TLabeled l1 t1) (TLabeled l2 t2)
   | isDBValue t1 && isDBValue t2
  && ςTerm t1 && ςTerm t2
  =   subst x (εTerm l tx) (εTerm l (TInsert n (TLabeled l1 t1) (TLabeled l2 t2))) 
  ==. subst x (εTerm l tx) (TInsert n (εTerm l (TLabeled l1 t1)) (εTerm l (TLabeled l2 t2))) 
  ==. substTInsert x (εTerm l tx) n (εTerm l (TLabeled l1 t1)) (εTerm l (TLabeled l2 t2)) 
  ==. subst x (εTerm l tx) (TInsert n (TLabeled l1 t1') (TLabeled l2 t2')) 
  ==. TInsert n (TLabeled l1 (subst x (εTerm l tx) t1')) 
                (TLabeled l2 (subst x (εTerm l tx) t2'))   
  ==. TInsert n (TLabeled l1 (if l1 `canFlowTo` l 
                               then subst x (εTerm l tx) (εTerm l t1) 
                               else subst x (εTerm l tx) THole)) 
                (TLabeled l2 (if l2 `canFlowTo` l 
                               then subst x (εTerm l tx) (εTerm l t2) 
                               else subst x (εTerm l tx) THole)) 
  ==. TInsert n (TLabeled l1 (if l1 `canFlowTo` l then subst x (εTerm l tx) (εTerm l t1) else THole)) 
                (TLabeled l2 (if l2 `canFlowTo` l then subst x (εTerm l tx) (εTerm l t2) else THole)) 
      ? homomorphicSubst l x tx t1 
      ? homomorphicSubst l x tx t2
  ==. TInsert n (TLabeled l1 (if l1 `canFlowTo` l then εTerm l (subst x tx t1) else THole)) 
                (TLabeled l2 (if l2 `canFlowTo` l then εTerm l (subst x tx t2) else THole)) 
  ==. TInsert n (εTerm l (TLabeled l1 (subst x tx t1))) 
                (εTerm l (TLabeled l2 (subst x tx t2))) 
  ==. TInsert n (εTerm l (subst x tx (TLabeled l1 t1)))
                (εTerm l (subst x tx (TLabeled l2 t2)))
  ==. εTerm l (TInsert n (subst x tx (TLabeled l1 t1)) 
                         (subst x tx (TLabeled l2 t2)))
  ==. εTerm l (substTInsert x tx n (TLabeled l1 t1) (TLabeled l2 t2))
  ==. εTerm l (subst x tx (TInsert n (TLabeled l1 t1) (TLabeled l2 t2)))
  *** QED 
    where
      t1' = if l1 `canFlowTo` l then εTerm l t1 else THole
      t2' = if l2 `canFlowTo` l then εTerm l t2 else THole

homomorphicSubstTInsert l x tx n t1 t2
  =   subst x (εTerm l tx) (εTerm l (TInsert n t1 t2)) 
  ==. subst x (εTerm l tx) (TInsert n (εTerm l t1) (εTerm l t2)) 
  ==. substTInsert x (εTerm l tx) n (εTerm l t1) (εTerm l t2) 
  ==. TInsert n (subst x (εTerm l tx) (εTerm l t1)) (subst x (εTerm l tx) (εTerm l t2)) 
      ? homomorphicSubst l x tx t1 
      ? homomorphicSubst l x tx t2
  ==. TInsert n (εTerm l (subst x tx t1)) (εTerm l (subst x tx t2)) 
  ==. εTerm l (substTInsert x tx n t1 t2)
  ==. εTerm l (subst x tx (TInsert n t1 t2))
  *** QED 

homomorphicSubstTUpdate :: (Label l, Eq l) => l -> Var -> Term l -> TName -> Term l -> Term l -> Term l -> Proof 
{-@ homomorphicSubstTUpdate 
  :: Label l => l:l -> x:Var -> tx:Term l -> n:TName -> t1:Term l -> t2:Term l -> t3:Term l  
  ->  { εTerm l (subst x tx (TUpdate n t1 t2 t3)) == subst x (εTerm l tx) (εTerm l (TUpdate n t1 t2 t3)) } 
  / [(1 + tsize t1 + tsize t2 + tsize t3), 0] @-}

homomorphicSubstTUpdate l x tx n (TPred p) (TLabeled l1 t1) (TLabeled l2 t2)
   | isDBValue t1 && isDBValue t2
  && ςTerm t1 && ςTerm t2
  =   subst x (εTerm l tx) (εTerm l (TUpdate n (TPred p) (TLabeled l1 t1) (TLabeled l2 t2))) 
  ==. subst x (εTerm l tx) (TUpdate n (εTerm l (TPred p)) (εTerm l (TLabeled l1 t1)) (εTerm l (TLabeled l2 t2))) 
  ==. subst x (εTerm l tx) (TUpdate n (TPred p) (TLabeled l1 t1') (TLabeled l2 t2')) 
  ==. substTUpdate x (εTerm l tx) n (TPred p) (TLabeled l1 t1') (TLabeled l2 t2')
  ==. TUpdate n (TPred (substPred x (εTerm l tx) p)) 
                (TLabeled l1 (subst x (εTerm l tx) t1')) 
                (TLabeled l2 (subst x (εTerm l tx) t2'))   
  ==. TUpdate n (TPred p)
                (TLabeled l1 (if l1 `canFlowTo` l 
                               then subst x (εTerm l tx) (εTerm l t1) 
                               else subst x (εTerm l tx) THole)) 
                (TLabeled l2 (if l2 `canFlowTo` l 
                               then subst x (εTerm l tx) (εTerm l t2) 
                               else subst x (εTerm l tx) THole)) 
  ==. TUpdate n (TPred p)
                (TLabeled l1 (if l1 `canFlowTo` l then subst x (εTerm l tx) (εTerm l t1) else THole)) 
                (TLabeled l2 (if l2 `canFlowTo` l then subst x (εTerm l tx) (εTerm l t2) else THole)) 
      ? homomorphicSubst l x tx t1 
      ? homomorphicSubst l x tx t2
  ==. TUpdate n (TPred p)
                (TLabeled l1 (if l1 `canFlowTo` l then εTerm l (subst x tx t1) else THole)) 
                (TLabeled l2 (if l2 `canFlowTo` l then εTerm l (subst x tx t2) else THole)) 
  ==. TUpdate n (εTerm l (TPred p))
                (εTerm l (TLabeled l1 (subst x tx t1))) 
                (εTerm l (TLabeled l2 (subst x tx t2))) 
  ==. TUpdate n (εTerm l (TPred p))
                (εTerm l (subst x tx (TLabeled l1 t1)))
                (εTerm l (subst x tx (TLabeled l2 t2)))
  ==. εTerm l (TUpdate n (TPred (substPred x tx p))
                         (subst x tx (TLabeled l1 t1)) 
                         (subst x tx (TLabeled l2 t2)))
  ==. εTerm l (substTUpdate x tx n (TPred p) (TLabeled l1 t1) (TLabeled l2 t2))
  ==. εTerm l (subst x tx (TUpdate n (TPred p) (TLabeled l1 t1) (TLabeled l2 t2)))
  *** QED 
    where
      t1' = if l1 `canFlowTo` l then εTerm l t1 else THole
      t2' = if l2 `canFlowTo` l then εTerm l t2 else THole 
      
homomorphicSubstTUpdate l x tx n t1 t2 t3
  =   subst x (εTerm l tx) (εTerm l (TUpdate n t1 t2 t3)) 
  ==. subst x (εTerm l tx) (TUpdate n (εTerm l t1) (εTerm l t2) (εTerm l t2)) 
  ==. substTUpdate x (εTerm l tx) n (εTerm l t1) (εTerm l t2) (εTerm l t3)
  ==. TUpdate n (subst x (εTerm l tx) (εTerm l t1)) 
                (subst x (εTerm l tx) (εTerm l t2)) 
                (subst x (εTerm l tx) (εTerm l t3)) 
      ? homomorphicSubst l x tx t1 
      ? homomorphicSubst l x tx t2
      ? homomorphicSubst l x tx t3
  ==. TUpdate n (εTerm l (subst x tx t1)) (εTerm l (subst x tx t2)) (εTerm l (subst x tx t3)) 
  ==. εTerm l (TUpdate n (subst x tx t1) (subst x tx t2) (subst x tx t3))
  ==. εTerm l (substTUpdate x tx n t1 t2 t3)
  ==. εTerm l (subst x tx (TUpdate n t1 t2 t3))
  *** QED        

-}  

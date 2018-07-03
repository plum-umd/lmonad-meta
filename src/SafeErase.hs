{-@ LIQUID "--reflection"  @-}

module SafeErase where

import ProofCombinators 
import Programs
import Labels 
import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ safeErase
  :: (Eq l, Label l) 
  => l:l 
  -> p:Program l 
  -> { ς p => ς (ε l p) } @-} -- the other directions does not hold!
safeErase  :: (Eq l, Label l) => l -> Program l -> Proof 
safeErase l (PgHole db) 
  =   ς (ε l (PgHole db))
  ==. ς (PgHole (εDB l db))
  ==. True 
  *** QED  

safeErase l (Pg lc db t) 
  | not (lc `canFlowTo` l)
  =   ς (ε l (Pg lc db t))
  ==. ς (PgHole (εDB l db))
  *** QED  

safeErase l (Pg lc db t) 
  =   ς (ε l (Pg lc db t))
  <=. ς (Pg lc (εDB l db) (εTerm l t))
  <=. ςTerm (εTerm l t)
      ? safeEraseTerm l t 
  ==. ςTerm t 
  ==. ς (Pg lc db t)
  *** QED 

{-@ safeEraseTerm 
  :: (Eq l, Label l) 
  => l:l 
  -> t:Term l 
  -> { ςTerm t => ςTerm (εTerm l t) } @-} -- the other directions does not hold! 
safeEraseTerm  :: (Eq l, Label l) => l -> Term l -> Proof 
safeEraseTerm l (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))
  =   ςTerm (εTerm l (TInsert n (TLabeled l1 v1) (TLabeled l2 v2)))
  ==. ςTerm (TInsert n (εTerm l (TLabeled l1 v1)) (εTerm l (TLabeled l2 v2)))
  ==. ςTerm (TInsert n (εTerm l (TLabeled l1 v1)) (εTerm l (TLabeled l2 v2)))
  ==. ςTerm (TInsert n (TLabeled l1 v1') (TLabeled l2 v2'))
  <=. (isDBValue v1' && isDBValue v2')
  <=. (isDBValue (εTerm l v1) && isDBValue (εTerm l v2))
      ? safeEraseTerm l v1 
      ? safeEraseTerm l v2 
  ==. (isDBValue v1 && isDBValue v2)
  ==. ςTerm (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))
  *** QED
  where 
  	v1' = if l1 `canFlowTo` l then (εTerm l v1) else THole
  	v2' = if l2 `canFlowTo` l then (εTerm l v2) else THole

safeEraseTerm l (TInsert n t1 t2)
  =   ςTerm (εTerm l (TInsert n t1 t2))
  ==. ςTerm (TInsert n (εTerm l t1) (εTerm l t2))
  <=. False 
  ==. ςTerm (TInsert n t1 t2)
  *** QED


safeEraseTerm l (TUpdate n p@(TPred _) (TLabeled l1 v1) (TLabeled l2 v2))
  =   ςTerm (εTerm l (TUpdate n p (TLabeled l1 v1) (TLabeled l2 v2)))
  ==. ςTerm (TUpdate n (εTerm l p) (εTerm l (TLabeled l1 v1)) (εTerm l (TLabeled l2 v2)))
  ==. ςTerm (TUpdate n (εTerm l p) (εTerm l (TLabeled l1 v1)) (εTerm l (TLabeled l2 v2)))
  ==. ςTerm (TUpdate n (εTerm l p) (TLabeled l1 v1') (TLabeled l2 v2'))
  <=. (isDBValue v1' && isDBValue v2')
  <=. (isDBValue (εTerm l v1) && isDBValue (εTerm l v2))
      ? safeEraseTerm l v1 
      ? safeEraseTerm l v2 
  ==. (εTerm l p == p && isDBValue v1 && isDBValue v2)
  ==. ςTerm (TUpdate n p (TLabeled l1 v1) (TLabeled l2 v2))
  *** QED
  where 
    v1' = if l1 `canFlowTo` l then (εTerm l v1) else THole
    v2' = if l2 `canFlowTo` l then (εTerm l v2) else THole

safeEraseTerm l (TUpdate n t1 t2 t3)
  =   ςTerm (εTerm l (TUpdate n t1 t2 t3))
  ==. ςTerm (TUpdate n (εTerm l t1) (εTerm l t2) (εTerm l t3))
  <=. False 
  ==. ςTerm (TUpdate n t1 t2 t3)
  *** QED



safeEraseTerm l (TInt i)
  =   ςTerm (εTerm l (TInt i))
  ==. ςTerm (TInt i)
  *** QED

safeEraseTerm l TUnit
  =   ςTerm (εTerm l TUnit)
  ==. ςTerm TUnit
  *** QED

safeEraseTerm l TTrue
  =   ςTerm (εTerm l TTrue)
  ==. ςTerm TTrue
  *** QED

safeEraseTerm l TFalse
  =   ςTerm (εTerm l TFalse)
  ==. ςTerm TFalse
  *** QED

safeEraseTerm l (TVLabel ll)
  =   ςTerm (εTerm l (TVLabel ll))
  ==. ςTerm (TVLabel ll)
  *** QED

safeEraseTerm l TNil
  =   ςTerm (εTerm l TNil)
  ==. ςTerm TNil
  *** QED

safeEraseTerm l (TCons t1 t2)
  =   ςTerm (εTerm l (TCons t1 t2))
  ==. ςTerm (TCons (εTerm l t1) (εTerm l t2))
  ==. (ςTerm (εTerm l t1) && ςTerm (εTerm l t2))
      ? safeEraseTerm l t1 
      ? safeEraseTerm l t2 
  ==. (ςTerm t1 && ςTerm t2)
  ==. ςTerm (TCons t1 t2)
  *** QED

safeEraseTerm l THole
  =   ςTerm (εTerm l THole)
  ==. ςTerm THole
  *** QED        

safeEraseTerm l (TSelect n t)
  =   ςTerm (εTerm l (TSelect n t))
  ==. ςTerm (TSelect n (εTerm l t))
  ==. ςTerm (εTerm l t)
      ? safeEraseTerm l t 
  ==. ςTerm t
  ==. ςTerm (TSelect n t)
  *** QED

safeEraseTerm l (TDelete n t)
  =   ςTerm (εTerm l (TDelete n t))
  ==. ςTerm (TDelete n (εTerm l t))
  ==. ςTerm (εTerm l t)
      ? safeEraseTerm l t 
  ==. ςTerm t
  ==. ςTerm (TDelete n t)
  *** QED

safeEraseTerm l (TLabeled ll t)
  | ll `canFlowTo` l 
  =   ςTerm (εTerm l (TLabeled ll t))
  ==. ςTerm (TLabeled ll (εTerm l t))
  ==. ςTerm (εTerm l t)
      ? safeEraseTerm l t 
  ==. ςTerm t
  ==. ςTerm (TLabeled ll t)
  *** QED
  | otherwise 
  =   ςTerm (εTerm l (TLabeled ll t))
  ==. ςTerm (TLabeled ll THole)
  ==. ςTerm THole
  <=. ςTerm t
  ==. ςTerm (TLabeled ll t)
  *** QED

safeEraseTerm l TException
  =   ςTerm (εTerm l TException)
  ==. ςTerm TException
  *** QED

safeEraseTerm l (TPred p)
  =   ςTerm (εTerm l (TPred p))
  ==. ςTerm (TPred p)
  *** QED

safeEraseTerm l (TIf t1 t2 t3)
  =   ςTerm (εTerm l (TIf t1 t2 t3))
  ==. ςTerm (TIf (εTerm l t1) (εTerm l t2) (εTerm l t3))
  ==. (ςTerm (εTerm l t1) && ςTerm (εTerm l t2) && ςTerm (εTerm l t3))
      ? safeEraseTerm l t1 
      ? safeEraseTerm l t2 
      ? safeEraseTerm l t3 
  ==. (ςTerm t1 && ςTerm t2 && ςTerm t3)
  ==. ςTerm (TIf t1 t2 t3)
  *** QED

safeEraseTerm l (TUnlabel t)
  =   ςTerm (εTerm l (TUnlabel t))
  ==. ςTerm (TUnlabel (εTerm l t))
  ==. ςTerm (εTerm l t)
      ? safeEraseTerm l t 
  ==. ςTerm t
  ==. ςTerm (TUnlabel t)
  *** QED

safeEraseTerm l (TBind t1 t2)
  =   ςTerm (εTerm l (TBind t1 t2))
  ==. ςTerm (TBind (εTerm l t1) (εTerm l t2))
  ==. (ςTerm (εTerm l t1) && ςTerm (εTerm l t2))
      ? safeEraseTerm l t1 
      ? safeEraseTerm l t2 
  ==. (ςTerm t1 && ςTerm t2)
  ==. ςTerm (TBind t1 t2)
  *** QED

safeEraseTerm l (TReturn t)
  =   ςTerm (εTerm l (TReturn t))
  ==. ςTerm (TReturn (εTerm l t))
  ==. ςTerm (εTerm l t)
      ? safeEraseTerm l t 
  ==. ςTerm t
  ==. ςTerm (TReturn t)
  *** QED

safeEraseTerm l (TLIO t)
  =   ςTerm (εTerm l (TLIO t))
  ==. ςTerm (TLIO (εTerm l t))
  ==. ςTerm (εTerm l t)
      ? safeEraseTerm l t 
  ==. ςTerm t
  ==. ςTerm (TLIO t)
  *** QED

safeEraseTerm l (TApp t1 t2)
  =   ςTerm (εTerm l (TApp t1 t2))
  ==. ςTerm (TApp (εTerm l t1) (εTerm l t2))
  ==. (ςTerm (εTerm l t1) && ςTerm (εTerm l t2))
      ? safeEraseTerm l t1 
      ? safeEraseTerm l t2 
  ==. (ςTerm t1 && ςTerm t2)
  ==. ςTerm (TApp t1 t2)
  *** QED

safeEraseTerm l (TLam x t)
  =   ςTerm (εTerm l (TLam x t))
  ==. ςTerm (TLam x (εTerm l t))
  ==. ςTerm (εTerm l t)
      ? safeEraseTerm l t 
  ==. ςTerm t
  ==. ςTerm (TLam x t)
  *** QED

safeEraseTerm l (TToLabeled t1 t2)
  =   ςTerm (εTerm l (TToLabeled t1 t2))
  ==. ςTerm (TToLabeled (εTerm l t1) (εTerm l t2))
  ==. (ςTerm (εTerm l t1) && ςTerm (εTerm l t2))
      ? safeEraseTerm l t1 
      ? safeEraseTerm l t2 
  ==. (ςTerm t1 && ςTerm t2)
  ==. ςTerm (TToLabeled t1 t2)
  *** QED  

safeEraseTerm l (TVar x)
  =   ςTerm (εTerm l (TVar x))
  ==. ςTerm (TVar x)
  *** QED
  
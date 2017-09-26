{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}
{-@ LIQUID "--trustinternals"                           @-}

{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}
module MetaFunctions where

import Language 
import Programs 

{-@ reflect evalEraseProgram @-}
evalEraseProgram :: Program -> Label -> Pair Index Program 
evalEraseProgram p l = mapSnd (ε l) (evalProgram p)

-------------------------------------------------------------------------------
-- | Erasure ------------------------------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect εTerm @-}
{-@ εTerm :: Label -> t:Term -> Term / [size t] @-} 
εTerm :: Label -> Term -> Term 
εTerm _ THole          = THole
εTerm _ TTrue          = TTrue
εTerm _ TFalse         = TFalse
εTerm _ TUnit          = TUnit
εTerm _ (TVar v)       = TVar v 
εTerm l (TLam v t)     = TLam v (εTerm l t)
εTerm l (TApp t1 t2)   = TApp (εTerm l t1) (εTerm l t2)
εTerm l (TFix t)       = TFix (εTerm l t) 
εTerm l (TIf t1 t2 t3) = TIf (εTerm l t1) (εTerm l t2) (εTerm l t3)

εTerm _ v@(TVLabel _)   = v
εTerm l (TJoin t1 t2)  = TJoin (εTerm l t1) (εTerm l t2)
εTerm l (TMeet t1 t2)  = TMeet (εTerm l t1) (εTerm l t2)
εTerm l (TCanFlowTo t1 t2) = TCanFlowTo (εTerm l t1) (εTerm l t2)

εTerm l (TBind t1 t2) = TBind (εTerm l t1) (εTerm l t2)

εTerm _ TGetLabel     = TGetLabel
εTerm _ TGetClearance = TGetClearance
εTerm l (TLowerClearance t) = TLowerClearance (εTerm l t)

εTerm l (TLabeledTCB l' t) | l' `canFlowTo` l = TLabeledTCB l' (εTerm l t)
εTerm _ (TLabeledTCB _ _) = THole

εTerm l (TLabelOf t) = TLabelOf (εTerm l t)

εTerm l (TLabel (TVLabel l') t2) | l' `canFlowTo` l = TLabel (TVLabel l') (εTerm l t2)
εTerm _ (TLabel (TVLabel _) _) = THole -- JP: This erasure might not be required.
εTerm l (TLabel t1 t2) = TLabel (εTerm l t1) (εTerm l t2)

εTerm l (TUnlabel t) = TUnlabel (εTerm l t)

εTerm _ TException = TException

{-@ reflect ε @-}
ε :: Label -> Program -> Program
ε l (Pg lcur c m t) 
  | lcur `canFlowTo` l 
  = Pg lcur c m (εTerm l t)
  | otherwise 
  = Pg lcur c m THole 

-------------------------------------------------------------------------------
-- | Safety -------------------------------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect ςTerm @-}
ςTerm :: Term -> Bool  
ςTerm THole          = True
ςTerm TTrue          = True
ςTerm TFalse         = True
ςTerm TUnit          = True
ςTerm (TVar _)       = True 
ςTerm (TLam _ t)     = ςTerm t
ςTerm (TApp t1 t2)   = ςTerm t1 && ςTerm t2
ςTerm (TFix t)       = ςTerm t 
ςTerm (TIf t1 t2 t3) = ςTerm t1 && ςTerm t2 && ςTerm t3

ςTerm (TVLabel _)       = True 
ςTerm (TJoin _ _)      = True 
ςTerm (TMeet _ _)      = True 
ςTerm (TCanFlowTo _ _) = True 

ςTerm (TBind _ _) = True 

ςTerm TGetLabel      = True 
ςTerm TGetClearance  = True 
ςTerm (TLowerClearance t)  = ςTerm t

ςTerm (TLabeledTCB _ _)  = False
ςTerm (TLabelOf t) = ςTerm t
ςTerm (TLabel t1 t2) = ςTerm t1 && ςTerm t2
ςTerm (TUnlabel t) = ςTerm t

ςTerm TException = True -- JP: Is this right?

{-@ reflect ς @-}
ς :: Program -> Bool 
ς (Pg _ _ _ t) = ςTerm t 


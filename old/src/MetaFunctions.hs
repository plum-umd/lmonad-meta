{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}
{-@ LIQUID "--trustinternals"                           @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}

module MetaFunctions where

import Label
import Language 
import Programs 
import ProofCombinators

{-@ reflect evalEraseProgram @-}
evalEraseProgram :: Program -> Label -> Program 
evalEraseProgram p l = ε l (evalProgram p)

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
εTerm _ (TLabeledTCB l' _) = TLabeledTCB l' THole
-- εTerm _ (TLabeledTCB _ _) = THole

εTerm l (TLabelOf t) = TLabelOf (εTerm l t)

εTerm l (TLabel t1 t2) = TLabel (εTerm l t1) (εTerm l t2)

εTerm l (TUnlabel t) = TUnlabel (εTerm l t)

εTerm l (TToLabeled t1 t2) = TToLabeled (εTerm l t1) (εTerm l t2)

εTerm _ TException = TException

{-@ reflect ε @-}
ε :: Label -> Program -> Program
ε _ PgHole = PgHole
ε l (Pg lcur c m t) 
  | lcur `canFlowTo` l 
  = Pg lcur c m (εTerm l t)
  | otherwise 
  = PgHole

-------------------------------------------------------------------------------
-- | Safety -------------------------------------------------------------------
-------------------------------------------------------------------------------

{-@ measure ςTerm @-}
ςTerm :: Term -> Bool  
ςTerm THole          = False
ςTerm TTrue          = True
ςTerm TFalse         = True
ςTerm TUnit          = True
ςTerm (TVar _)       = True 
ςTerm (TLam _ t)     = ςTerm t
ςTerm (TApp t1 t2)   = ςTerm t1 && ςTerm t2
ςTerm (TFix t)       = ςTerm t 
ςTerm (TIf t1 t2 t3) = ςTerm t1 && ςTerm t2 && ςTerm t3

ςTerm (TVLabel _)        = True 
ςTerm (TJoin t1 t2)      = ςTerm t1 && ςTerm t2
ςTerm (TMeet t1 t2)      = ςTerm t1 && ςTerm t2
ςTerm (TCanFlowTo t1 t2) = ςTerm t1 && ςTerm t2

ςTerm (TBind t1 t2) = ςTerm t1 && ςTerm t2

ςTerm TGetLabel      = True 
ςTerm TGetClearance  = True 
ςTerm (TLowerClearance t)  = ςTerm t

ςTerm (TLabeledTCB _ _)  = False
ςTerm (TLabelOf t) = ςTerm t
ςTerm (TLabel t1 t2) = ςTerm t1 && ςTerm t2
ςTerm (TUnlabel t) = ςTerm t

ςTerm (TToLabeled t1 t2) = ςTerm t1 && ςTerm t2

ςTerm TException = True -- JP: Is this right?

{-@ measure ς @-}
ς :: Program -> Bool 
ς (Pg _ _ _ t) = ςTerm t 
ς PgHole = False

-- {-@ inv_isTLam
--  :: v:Term
--  -> { isTLam v <=> is$Language.TLam v}
--  @-}
-- inv_isTLam :: Term -> Proof
-- inv_isTLam (TLam _ _) = trivial
-- inv_isTLam _          = trivial
-- 
-- {-@ eraseNotTLam
--  :: l : Label
--  -> t : {Term | not (isTLam t)}
--  -> {not (isTLam (εTerm l t))}
--  @-}
-- eraseNotTLam :: Label -> Term -> Proof
-- eraseNotTLam _ _ = ()
-- 
-- {-@ inv_isTVLabel 
--     :: v:Term 
--     -> { isTVLabel v <=> is$Language.TVLabel v}
--     @-}
-- inv_isTVLabel :: Term -> Proof
-- inv_isTVLabel (TVLabel _) = trivial
-- inv_isTVLabel _           = trivial

{-@ eraseNotTVLabel
 :: l : Label
 -> t : {Term | not (is$Language.TVLabel t)}
 -> {not (isTVLabel (εTerm l t))}
 @-}
eraseNotTVLabel :: Label -> Term -> Proof
eraseNotTVLabel l t@(TLam v t1) = 
        εTerm l t
    ==. (TLam v (εTerm l t1))
    *** QED

eraseNotTVLabel l t@(TApp t1 t2) = 
        εTerm l t
    ==. (TApp (εTerm l t1) (εTerm l t2))
    *** QED

eraseNotTVLabel l t@(TFix t1) = 
        εTerm l t
    ==. (TFix (εTerm l t1))
    *** QED

eraseNotTVLabel l t@(TIf t1 t2 t3) = 
        εTerm l t
    ==. (TIf (εTerm l t1) (εTerm l t2) (εTerm l t3))
    *** QED

eraseNotTVLabel l t@(TJoin t1 t2) = 
        εTerm l t
    ==. (TJoin (εTerm l t1) (εTerm l t2))
    *** QED

eraseNotTVLabel l t@(TMeet t1 t2) = 
        εTerm l t
    ==. (TMeet (εTerm l t1) (εTerm l t2))
    *** QED

eraseNotTVLabel l t@(TCanFlowTo t1 t2) = 
        εTerm l t
    ==. (TCanFlowTo (εTerm l t1) (εTerm l t2))
    *** QED

eraseNotTVLabel l t@(TBind t1 t2) = 
        εTerm l t
    ==. (TBind (εTerm l t1) (εTerm l t2))
    *** QED

eraseNotTVLabel l t@(TLowerClearance t1) = 
        εTerm l t
    ==. (TLowerClearance (εTerm l t1))
    *** QED

eraseNotTVLabel l t@(TLabeledTCB l' t1) | l' `canFlowTo` l = 
        εTerm l t
    ==. (TLabeledTCB l' (εTerm l t1))
    *** QED

eraseNotTVLabel l t@(TLabeledTCB l' t1) = 
        εTerm l t
    ==. (TLabeledTCB l' THole)
    *** QED

eraseNotTVLabel l t@(TLabelOf t1) = 
        εTerm l t
    ==. (TLabelOf (εTerm l t1))
    *** QED

eraseNotTVLabel l t@(TLabel t1 t2) = 
        εTerm l t
    ==. (TLabel (εTerm l t1) (εTerm l t2))
    *** QED

eraseNotTVLabel l t@(TUnlabel t1) = 
        εTerm l t
    ==. (TUnlabel (εTerm l t1))
    *** QED

eraseNotTVLabel l t@(TVLabel _) = unreachable

eraseNotTVLabel l t@(TToLabeled t1 t2) = 
        εTerm l t
    ==. (TToLabeled (εTerm l t1) (εTerm l t2))
    *** QED

eraseNotTVLabel l t = 
        εTerm l t
    *** QED


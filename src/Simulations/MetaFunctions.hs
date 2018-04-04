{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}

module Simulations.MetaFunctions where

import Label
import Language
import Programs
import MetaFunctions

import ProofCombinators

{-@ εTermIdempotent 
 :: l : Label 
 -> t : Term 
 -> {v : Proof | εTerm l (εTerm l t) == εTerm l t}
 / [size t]
 @-}
εTermIdempotent :: Label -> Term -> Proof
εTermIdempotent l t@(TLabeledTCB l' t1) | l' `canFlowTo` l = 
        εTerm l (εTerm l t)
    ==! εTerm l (TLabeledTCB l' (εTerm l t1))
    ==! TLabeledTCB l' (εTerm l (εTerm l t1))
    ==: TLabeledTCB l' (εTerm l (εTerm l t1)) ? εTermIdempotent l t1
    ==! εTerm l t
    *** QED
εTermIdempotent l t@(TLabeledTCB l' _) =
        εTerm l (εTerm l t)
    ==! εTerm l (TLabeledTCB l' THole)
    ==! TLabeledTCB l' THole
    ==! εTerm l t
    *** QED

εTermIdempotent l t@(TLabel t1 t2) = 
        εTerm l (εTerm l t)
    ==! εTerm l (TLabel (εTerm l t1) (εTerm l t2))
    ==! TLabel (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2))
    ==: TLabel (εTerm l t1) (εTerm l t2) ? εTermIdempotent l t1 &&& εTermIdempotent l t2
    ==! εTerm l t
    *** QED

εTermIdempotent l t@(TLam v t1) = 
        εTerm l (εTerm l t)
    ==! εTerm l (TLam v (εTerm l t1))
    ==! TLam v (εTerm l (εTerm l t1))
    ==: TLam v (εTerm l (εTerm l t1)) ? εTermIdempotent l t1
    ==! εTerm l t
    *** QED

εTermIdempotent l t@(TApp t1 t2) = 
        εTerm l (εTerm l t)
    ==! εTerm l (TApp (εTerm l t1) (εTerm l t2))
    ==! TApp (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2))
    ==: TApp (εTerm l t1) (εTerm l t2) ? εTermIdempotent l t1 &&& εTermIdempotent l t2
    ==! εTerm l t
    *** QED

εTermIdempotent l t@(TFix t1) = 
        εTerm l (εTerm l t)
    ==! εTerm l (TFix (εTerm l t1))
    ==! TFix (εTerm l (εTerm l t1))
    ==: TFix (εTerm l t1) ? εTermIdempotent l t1
    ==! εTerm l t
    *** QED

εTermIdempotent l t@(TIf t1 t2 t3) = 
        εTerm l (εTerm l t)
    ==! εTerm l (TIf (εTerm l t1) (εTerm l t2) (εTerm l t3))
    ==! TIf (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2)) (εTerm l (εTerm l t3))
    ==: TIf (εTerm l t1) (εTerm l t2) (εTerm l t3) ? εTermIdempotent l t1 &&& εTermIdempotent l t2 &&& εTermIdempotent l t3
    ==! εTerm l t
    *** QED

εTermIdempotent l t@(TJoin t1 t2) = 
        εTerm l (εTerm l t)
    ==! εTerm l (TJoin (εTerm l t1) (εTerm l t2))
    ==! TJoin (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2))
    ==: TJoin (εTerm l t1) (εTerm l t2) ? εTermIdempotent l t1 &&& εTermIdempotent l t2
    ==! εTerm l t
    *** QED

εTermIdempotent l t@(TMeet t1 t2) = 
        εTerm l (εTerm l t)
    ==! εTerm l (TMeet (εTerm l t1) (εTerm l t2))
    ==! TMeet (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2))
    ==: TMeet (εTerm l t1) (εTerm l t2) ? εTermIdempotent l t1 &&& εTermIdempotent l t2
    ==! εTerm l t
    *** QED

εTermIdempotent l t@(TCanFlowTo t1 t2) = 
        εTerm l (εTerm l t)
    ==! εTerm l (TCanFlowTo (εTerm l t1) (εTerm l t2))
    ==! TCanFlowTo (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2))
    ==: TCanFlowTo (εTerm l t1) (εTerm l t2) ? εTermIdempotent l t1 &&& εTermIdempotent l t2
    ==! εTerm l t
    *** QED

εTermIdempotent l t@(TBind t1 t2) = 
        εTerm l (εTerm l t)
    ==! εTerm l (TBind (εTerm l t1) (εTerm l t2))
    ==! TBind (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2))
    ==: TBind (εTerm l t1) (εTerm l t2) ? εTermIdempotent l t1 &&& εTermIdempotent l t2
    ==! εTerm l t
    *** QED

εTermIdempotent l t@(TLowerClearance t1) = 
        εTerm l (εTerm l t)
    ==! εTerm l (TLowerClearance (εTerm l t1))
    ==! TLowerClearance (εTerm l (εTerm l t1))
    ==: TLowerClearance (εTerm l t1) ? εTermIdempotent l t1
    ==! εTerm l t
    *** QED

εTermIdempotent l t@(TLabelOf t1) = 
        εTerm l (εTerm l t)
    ==! εTerm l (TLabelOf (εTerm l t1))
    ==! TLabelOf (εTerm l (εTerm l t1))
    ==: TLabelOf (εTerm l t1) ? εTermIdempotent l t1
    ==! εTerm l t
    *** QED

εTermIdempotent l t@(TUnlabel t1) = 
        εTerm l (εTerm l t)
    ==! εTerm l (TUnlabel (εTerm l t1))
    ==! TUnlabel (εTerm l (εTerm l t1))
    ==: TUnlabel (εTerm l t1) ? εTermIdempotent l t1
    ==! εTerm l t
    *** QED

εTermIdempotent l t@(TToLabeled t1 t2) = 
        εTerm l (εTerm l t)
    ==! εTerm l (TToLabeled (εTerm l t1) (εTerm l t2))
    ==! TToLabeled (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2))
    ==: TToLabeled (εTerm l t1) (εTerm l t2) ? εTermIdempotent l t1 &&& εTermIdempotent l t2
    ==! εTerm l t
    *** QED

εTermIdempotent l t = 
        εTerm l (εTerm l t)
    ==! εTerm l t
    *** QED


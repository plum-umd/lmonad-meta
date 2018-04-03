{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}

module Simulations.EraseSubErase where

import Label
import Language
import Programs
import MetaFunctions
import Simulations.MetaFunctions

import ProofCombinators

{-@ eraseSubErase
 :: l : Label 
 -> x : Var 
 -> t1 : Term 
 -> t2 : Term 
 -> {v : Proof | εTerm l (subst (Sub x (εTerm l t1)) (εTerm l t2)) == εTerm l (subst (Sub x t1) t2) }
 / [size t2]
 @-}
eraseSubErase :: Label -> Var -> Term -> Term -> Proof
eraseSubErase l x t1 t2@(TVar y) =
    if x == y then
            εTerm l (subst (Sub x (εTerm l t1)) (εTerm l t2))
        ==. εTerm l (subst (Sub x (εTerm l t1)) t2)
        ==. εTerm l (εTerm l t1)
        ==. εTerm l t1 ? εTermIdempotent l t1
        ==. εTerm l (subst (Sub x t1) t2)
        *** QED
    else
            εTerm l (subst (Sub x (εTerm l t1)) (εTerm l t2))
        ==. εTerm l (subst (Sub x (εTerm l t1)) t2)
        ==. εTerm l t2
        ==. εTerm l (subst (Sub x t1) t2)
        *** QED
            
eraseSubErase l x t1 t2@(TLam y e) =
    if x == y then
            εTerm l (subst (Sub x (εTerm l t1)) (εTerm l t2))
        ==. εTerm l (subst (Sub x (εTerm l t1)) (TLam y (εTerm l e)))
        ==. εTerm l (TLam y (εTerm l e))
        ==. εTerm l (εTerm l (TLam y e))
        ==. εTerm l (TLam y e) ? εTermIdempotent l t2
        ==. εTerm l (subst (Sub x t1) t2)
        *** QED
    else
            εTerm l (subst (Sub x (εTerm l t1)) (εTerm l t2))
        ==. εTerm l (subst (Sub x (εTerm l t1)) (TLam y (εTerm l e)))
        ==. εTerm l (TLam y (subst (Sub x (εTerm l t1)) (εTerm l e)))
        ==. TLam y (εTerm l (subst (Sub x (εTerm l t1)) (εTerm l e)))
        ==. TLam y (εTerm l (subst (Sub x t1) e)) ? eraseSubErase l x t1 e
        ==. εTerm l (subst (Sub x t1) t2)
        *** QED

eraseSubErase l x t1 t2@(TApp t2a t2b) = 
        εTerm l (subst (Sub x (εTerm l t1)) (εTerm l t2))
    ==. εTerm l (subst esu (TApp (εTerm l t2a) (εTerm l t2b)))
    ==. εTerm l (TApp (subst esu (εTerm l t2a)) (subst esu (εTerm l t2b)))
    ==. TApp (εTerm l (subst esu (εTerm l t2a))) (εTerm l (subst esu (εTerm l t2b)))
    ==. TApp (εTerm l (subst su t2a)) (εTerm l (subst su t2b))
        ? eraseSubErase l x t1 t2a
        &&& eraseSubErase l x t1 t2b
    ==. εTerm l (subst (Sub x t1) t2)
    *** QED

    where 
        esu = Sub x (εTerm l t1)
        su = Sub x t1

eraseSubErase l x t' t@(TFix t1) = 
        εTerm l (subst (Sub x (εTerm l t')) (εTerm l t))
    ==. εTerm l (subst esu (TFix (εTerm l t1)))
    ==. εTerm l (TFix (subst esu (εTerm l t1)))
    ==. TFix (εTerm l (subst esu (εTerm l t1)))
    ==. TFix (εTerm l (subst su t1))
        ? eraseSubErase l x t' t1
    ==. εTerm l (subst (Sub x t') t)
    *** QED

    where 
        esu = Sub x (εTerm l t')
        su = Sub x t'

eraseSubErase l x t' t@(TIf t1 t2 t3) = 
        εTerm l (subst (Sub x (εTerm l t')) (εTerm l t))
    ==. εTerm l (subst (Sub x (εTerm l t')) (TIf (εTerm l t1) (εTerm l t2) (εTerm l t3)))
    ==. εTerm l (TIf (subst esu (εTerm l t1)) (subst esu (εTerm l t2)) (subst esu (εTerm l t3)))
    ==. εTerm l (TIf (subst su t1) (subst su t2) (subst su t3))
        ? eraseSubErase l x t' t1
        &&& eraseSubErase l x t' t2
        &&& eraseSubErase l x t' t3
    ==. εTerm l (subst (Sub x t') t)
    *** QED

    where 
        esu = Sub x (εTerm l t')
        su = Sub x t'

eraseSubErase l x t' t@(TJoin t1 t2) = 
        εTerm l (subst (Sub x (εTerm l t')) (εTerm l t))
    ==. εTerm l (subst (Sub x (εTerm l t')) (TJoin (εTerm l t1) (εTerm l t2)))
    ==. εTerm l (TJoin (subst esu (εTerm l t1)) (subst esu (εTerm l t2)))
    ==. εTerm l (TJoin (subst su t1) (subst su t2))
        ? eraseSubErase l x t' t1
        &&& eraseSubErase l x t' t2
    ==. εTerm l (subst (Sub x t') t)
    *** QED

    where 
        esu = Sub x (εTerm l t')
        su = Sub x t'

eraseSubErase l x t' t@(TMeet t1 t2) = 
        εTerm l (subst (Sub x (εTerm l t')) (εTerm l t))
    ==. εTerm l (subst (Sub x (εTerm l t')) (TMeet (εTerm l t1) (εTerm l t2)))
    ==. εTerm l (TMeet (subst esu (εTerm l t1)) (subst esu (εTerm l t2)))
    ==. εTerm l (TMeet (subst su t1) (subst su t2))
        ? eraseSubErase l x t' t1
        &&& eraseSubErase l x t' t2
    ==. εTerm l (subst (Sub x t') t)
    *** QED

    where 
        esu = Sub x (εTerm l t')
        su = Sub x t'

eraseSubErase l x t' t@(TCanFlowTo t1 t2) = 
        εTerm l (subst (Sub x (εTerm l t')) (εTerm l t))
    ==. εTerm l (subst (Sub x (εTerm l t')) (TCanFlowTo (εTerm l t1) (εTerm l t2)))
    ==. εTerm l (TCanFlowTo (subst esu (εTerm l t1)) (subst esu (εTerm l t2)))
    ==. εTerm l (TCanFlowTo (subst su t1) (subst su t2))
        ? eraseSubErase l x t' t1
        &&& eraseSubErase l x t' t2
    ==. εTerm l (subst (Sub x t') t)
    *** QED

    where 
        esu = Sub x (εTerm l t')
        su = Sub x t'

eraseSubErase l x t' t@(TBind t1 t2) = 
        εTerm l (subst (Sub x (εTerm l t')) (εTerm l t))
    ==. εTerm l (subst (Sub x (εTerm l t')) (TBind (εTerm l t1) (εTerm l t2)))
    ==. εTerm l (TBind (subst esu (εTerm l t1)) (subst esu (εTerm l t2)))
    ==. εTerm l (TBind (subst su t1) (subst su t2))
        ? eraseSubErase l x t' t1
        &&& eraseSubErase l x t' t2
    ==. εTerm l (subst (Sub x t') t)
    *** QED

    where 
        esu = Sub x (εTerm l t')
        su = Sub x t'

eraseSubErase l x t' t@(TLowerClearance t1) = 
        εTerm l (subst (Sub x (εTerm l t')) (εTerm l t))
    ==. εTerm l (subst esu (TLowerClearance (εTerm l t1)))
    ==. εTerm l (TLowerClearance (subst esu (εTerm l t1)))
    ==. TLowerClearance (εTerm l (subst esu (εTerm l t1)))
    ==. TLowerClearance (εTerm l (subst su t1))
        ? eraseSubErase l x t' t1
    ==. εTerm l (subst (Sub x t') t)
    *** QED

    where 
        esu = Sub x (εTerm l t')
        su = Sub x t'

eraseSubErase l x t' t@(TLabeledTCB ll t1) = 
    if ll `canFlowTo` l then
            εTerm l (subst (Sub x (εTerm l t')) (εTerm l t))
        ==. εTerm l (subst esu (TLabeledTCB ll (εTerm l t1)))
        ==. εTerm l (TLabeledTCB ll (εTerm l t1))
        ==. TLabeledTCB ll (εTerm l (εTerm l t1))
        ==. TLabeledTCB ll (εTerm l t1)
            ? εTermIdempotent l t1
        ==. εTerm l (subst (Sub x t') t)
        *** QED
    else
            εTerm l (subst (Sub x (εTerm l t')) (εTerm l t))
        ==. εTerm l (subst esu (TLabeledTCB ll THole))
        ==. εTerm l (subst esu (TLabeledTCB ll (εTerm l THole)))
        ==. εTerm l (subst su (TLabeledTCB ll THole))
            ? eraseSubErase l x t' THole
        ==. εTerm l (subst (Sub x t') t)
        *** QED

    where 
        esu = Sub x (εTerm l t')
        su = Sub x t'

eraseSubErase l x t' t@(TLabelOf t1) = 
        εTerm l (subst (Sub x (εTerm l t')) (εTerm l t))
    ==. εTerm l (subst esu (TLabelOf (εTerm l t1)))
    ==. εTerm l (TLabelOf (subst esu (εTerm l t1)))
    ==. TLabelOf (εTerm l (subst esu (εTerm l t1)))
    ==. TLabelOf (εTerm l (subst su t1))
        ? eraseSubErase l x t' t1
    ==. εTerm l (subst (Sub x t') t)
    *** QED

    where 
        esu = Sub x (εTerm l t')
        su = Sub x t'

eraseSubErase l x t' t@(TLabel t1 t2) = 
        εTerm l (subst (Sub x (εTerm l t')) (εTerm l t))
    ==. εTerm l (subst (Sub x (εTerm l t')) (TLabel (εTerm l t1) (εTerm l t2)))
    ==. εTerm l (TLabel (subst esu (εTerm l t1)) (subst esu (εTerm l t2)))
    ==. εTerm l (TLabel (subst su t1) (subst su t2))
        ? eraseSubErase l x t' t1
        &&& eraseSubErase l x t' t2
    ==. εTerm l (subst (Sub x t') t)
    *** QED

    where 
        esu = Sub x (εTerm l t')
        su = Sub x t'

eraseSubErase l x t' t@(TUnlabel t1) = 
        εTerm l (subst (Sub x (εTerm l t')) (εTerm l t))
    ==. εTerm l (subst esu (TUnlabel (εTerm l t1)))
    ==. εTerm l (TUnlabel (subst esu (εTerm l t1)))
    ==. TUnlabel (εTerm l (subst esu (εTerm l t1)))
    ==. TUnlabel (εTerm l (subst su t1))
        ? eraseSubErase l x t' t1
    ==. εTerm l (subst (Sub x t') t)
    *** QED

    where 
        esu = Sub x (εTerm l t')
        su = Sub x t'

eraseSubErase l x t' t@(TToLabeled t1 t2) = 
        εTerm l (subst (Sub x (εTerm l t')) (εTerm l t))
    ==. εTerm l (subst (Sub x (εTerm l t')) (TToLabeled (εTerm l t1) (εTerm l t2)))
    ==. εTerm l (TToLabeled (subst esu (εTerm l t1)) (subst esu (εTerm l t2)))
    ==. εTerm l (TToLabeled (subst su t1) (subst su t2))
        ? eraseSubErase l x t' t1
        &&& eraseSubErase l x t' t2
    ==. εTerm l (subst (Sub x t') t)
    *** QED

    where 
        esu = Sub x (εTerm l t')
        su = Sub x t'

eraseSubErase l x t1 t2 = 
        εTerm l (subst (Sub x (εTerm l t1)) (εTerm l t2))
    ==. εTerm l (subst (Sub x t1) t2)
    *** QED


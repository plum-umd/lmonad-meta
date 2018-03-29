{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}
{-@ LIQUID "--no-case-expand"                           @-}

module Simulations.EraseEvalErase where

import Label
import Language
import Programs
import MetaFunctions
import Simulations.EraseSubErase
import Simulations.Language
import Simulations.MetaFunctions

import LiquidHaskell.ProofCombinators

{-@ eraseEvalEraseSimulation
 :: l : Label 
 -> t : {Term | not (propagateException t)}
 -> {εTerm l (eval (εTerm l t)) == εTerm l (eval t)}
 / [size t]
 @-}
eraseEvalEraseSimulation :: Label -> Term -> Proof
eraseEvalEraseSimulation l t@(TIf t1 t2 t3) | isTTrue t1 = 
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (εTerm l (TIf TTrue t2 t3))) ? eqTTrue t1 -- JP: Why do we need this? XXX
    ==. εTerm l (eval (TIf (εTerm l TTrue) (εTerm l t2) (εTerm l t3)))
    ==. εTerm l (eval (TIf TTrue (εTerm l t2) (εTerm l t3)))
    ==. εTerm l (εTerm l t2) ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalse l t
    ==. εTerm l t2 ? εTermIdempotent l t2
    ==. εTerm l (eval t)
    *** QED

eraseEvalEraseSimulation l t@(TIf t1 t2 t3) | isTFalse t1 = 
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TIf (εTerm l TFalse) (εTerm l t2) (εTerm l t3))) ? eqTFalse t1
    ==. εTerm l (eval (TIf TFalse (εTerm l t2) (εTerm l t3)))
    ==. εTerm l (εTerm l t3) ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalse l t
    ==. εTerm l t3 ? εTermIdempotent l t3
    ==. εTerm l (eval t)
    *** QED

eraseEvalEraseSimulation l t@(TIf t1 t2 t3) = 
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TIf (εTerm l t1) (εTerm l t2) (εTerm l t3)))
    ==. εTerm l (TIf (eval (εTerm l t1)) (εTerm l t2) (εTerm l t3)) ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalse l t
    ==. TIf (εTerm l (eval (εTerm l t1))) (εTerm l (εTerm l t2)) (εTerm l (εTerm l t3))
    ==. TIf (εTerm l (eval (εTerm l t1))) (εTerm l t2) (εTerm l t3) ? εTermIdempotent l t2 &&& εTermIdempotent l t3
    ==. TIf (εTerm l (eval t1)) (εTerm l t2) (εTerm l t3) ? eraseEvalEraseSimulation l t1
    ==. εTerm l (eval t)
    *** QED

-- eraseEvalEraseSimulation l t@(TFix (TLam x t1)) = 
eraseEvalEraseSimulation l t@(TFix t1') | (TLam x t1) <- t1' = 
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TFix (εTerm l (TLam x t1))))
    ==. εTerm l (eval (TFix (TLam x (εTerm l t1))))
    ==. εTerm l (subst (Sub x (TFix (TLam x (εTerm l t1)))) (εTerm l t1)) ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalse l t
    ==. εTerm l (subst (Sub x (TFix (εTerm l (TLam x t1)))) (εTerm l t1))
    ==. εTerm l (subst (Sub x (εTerm l (TFix (TLam x t1)))) (εTerm l t1))
    ==. εTerm l (subst (Sub x (TFix (TLam x t1))) t1)
        ? eraseSubErase l x (TFix (TLam x t1)) t1
    ==. εTerm l (eval t)
    *** QED

eraseEvalEraseSimulation l t@(TFix t1) = 
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TFix (εTerm l t1)))
    ==. εTerm l (TFix (eval (εTerm l t1))) ? 
            propagateExceptionFalseEvalsToNonexception t 
        &&& erasePropagateExceptionFalse l t
        &&& eraseNotTLam l t1
    ==. TFix (εTerm l (eval (εTerm l t1)))
    ==. TFix (εTerm l (eval t1)) ? eraseEvalEraseSimulation l t1
    ==. εTerm l (eval t)
    *** QED

eraseEvalEraseSimulation l t@(TApp t1' t2) | TLam x t1 <- t1' = 
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TApp (εTerm l (TLam x t1)) (εTerm l t2)))
    ==. εTerm l (eval (TApp (TLam x (εTerm l t1)) (εTerm l t2)))
    ==. εTerm l (subst (Sub x (εTerm l t2)) (εTerm l t1))
        ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalse l t
    ==. εTerm l (subst (Sub x t2) t1)
        ? eraseSubErase l x t2 t1
    ==. εTerm l (eval t)
    *** QED

eraseEvalEraseSimulation l t@(TApp t1 t2) = 
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TApp (εTerm l t1) (εTerm l t2)))
    ==. εTerm l (TApp (eval (εTerm l t1)) (εTerm l t2)) ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalse l t
        &&& eraseNotTLam l t1
    ==. TApp (εTerm l (eval (εTerm l t1))) (εTerm l (εTerm l t2))
    ==. TApp (εTerm l (eval t1)) (εTerm l (εTerm l t2)) ? eraseEvalEraseSimulation l t1 &&& εTermIdempotent l t2
    ==. εTerm l (eval t)
    *** QED


eraseEvalEraseSimulation l t@(TJoin t1 t2) | TVLabel l1 <- t1, TVLabel l2 <- t2 = 
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TJoin (εTerm l (TVLabel l1)) (εTerm l (TVLabel l2))))
    ==. εTerm l (eval (TJoin t1 t2))
    ==. εTerm l (eval t)
    *** QED

eraseEvalEraseSimulation l t@(TJoin t1 t2) | TVLabel l1 <- t1 = 
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TJoin (εTerm l (TVLabel l1)) (εTerm l t2)))
    ==. εTerm l (eval (TJoin t1 (εTerm l t2)))
    ==. εTerm l (TJoin t1 (eval (εTerm l t2))) 
        ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalse l t
    ==. TJoin (εTerm l t1) (εTerm l (eval (εTerm l t2)))
    ==. TJoin t1 (εTerm l (eval t2)) ? eraseEvalEraseSimulation l t2
    ==. εTerm l (eval t)
    *** QED


eraseEvalEraseSimulation l t@(TJoin t1 t2) = 
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TJoin (εTerm l t1) (εTerm l t2)))
    ==. εTerm l (TJoin (eval (εTerm l t1)) (εTerm l t2))
        ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalse l t
    ==. TJoin (εTerm l (eval (εTerm l t1))) (εTerm l (εTerm l t2))
    ==. TJoin (εTerm l (eval t1)) (εTerm l t2)
        ? eraseEvalEraseSimulation l t1 
        &&& εTermIdempotent l t2
    ==. εTerm l (eval t)
    *** QED

eraseEvalEraseSimulation l t@(TMeet t1 t2) | TVLabel l1 <- t1, TVLabel l2 <- t2 = 
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TMeet (εTerm l (TVLabel l1)) (εTerm l (TVLabel l2))))
    ==. εTerm l (eval (TMeet t1 t2))
    ==. εTerm l (eval t)
    *** QED

eraseEvalEraseSimulation l t@(TMeet t1 t2) | TVLabel l1 <- t1 = 
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TMeet (εTerm l (TVLabel l1)) (εTerm l t2)))
    ==. εTerm l (eval (TMeet t1 (εTerm l t2)))
    ==. εTerm l (TMeet t1 (eval (εTerm l t2))) 
        ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalse l t
    ==. TMeet (εTerm l t1) (εTerm l (eval (εTerm l t2)))
    ==. TMeet t1 (εTerm l (eval t2)) ? eraseEvalEraseSimulation l t2
    ==. εTerm l (eval t)
    *** QED

eraseEvalEraseSimulation l t@(TMeet t1 t2) | not (isTVLabel t1) = 
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TMeet (εTerm l t1) (εTerm l t2)))
    ==. εTerm l (TMeet (eval (εTerm l t1)) (εTerm l t2))
        ? propagateExceptionFalseEvalsToNonexception t 
        &&& erasePropagateExceptionFalse l t
        &&& eraseNotTVLabel l t1
    ==. TMeet (εTerm l (eval (εTerm l t1))) (εTerm l (εTerm l t2))
    ==. TMeet (εTerm l (eval t1)) (εTerm l t2)
        ? eraseEvalEraseSimulation l t1 
        &&& εTermIdempotent l t2
    ==. εTerm l (eval t)
    *** QED


eraseEvalEraseSimulation l t@(TCanFlowTo t1 t2) | TVLabel l1 <- t1, TVLabel l2 <- t2 = 
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TCanFlowTo (εTerm l (TVLabel l1)) (εTerm l (TVLabel l2))))
    ==. εTerm l (eval (TCanFlowTo t1 t2))
    ==. εTerm l (eval t)
    *** QED

eraseEvalEraseSimulation l t@(TCanFlowTo t1 t2) | TVLabel l1 <- t1 = 
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TCanFlowTo (εTerm l (TVLabel l1)) (εTerm l t2)))
    ==. εTerm l (eval (TCanFlowTo t1 (εTerm l t2)))
    ==. εTerm l (TCanFlowTo t1 (eval (εTerm l t2))) 
        ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalse l t
    ==. TCanFlowTo (εTerm l t1) (εTerm l (eval (εTerm l t2)))
    ==. TCanFlowTo t1 (εTerm l (eval t2)) ? eraseEvalEraseSimulation l t2
    ==. εTerm l (eval t)
    *** QED

eraseEvalEraseSimulation l t@(TCanFlowTo t1 t2) = 
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TCanFlowTo (εTerm l t1) (εTerm l t2)))
    ==. εTerm l (TCanFlowTo (eval (εTerm l t1)) (εTerm l t2))
        ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalse l t
    ==. TCanFlowTo (εTerm l (eval (εTerm l t1))) (εTerm l (εTerm l t2))
    ==. TCanFlowTo (εTerm l (eval t1)) (εTerm l t2)
        ? eraseEvalEraseSimulation l t1 
        &&& εTermIdempotent l t2
    ==. εTerm l (eval t)
    *** QED

eraseEvalEraseSimulation l t@(TUnlabel t1) = 
        εTerm l (eval (εTerm l t))
    ==. εTerm l (TUnlabel (eval (εTerm l t1)))
        ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalse l t
    ==. TUnlabel (εTerm l (eval (εTerm l t1)))
    ==. TUnlabel (εTerm l (eval t1))
        ? eraseEvalEraseSimulation l t1
    ==. εTerm l (eval t)
    *** QED

eraseEvalEraseSimulation l t@(TLabel t1 t2) | (TVLabel l1) <- t1 = 
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TLabel (εTerm l (TVLabel l1)) (εTerm l t2)))
    ==. εTerm l (TLabel (εTerm l t1) (eval (εTerm l t2)))
        ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalse l t
    ==. TLabel (εTerm l (εTerm l t1)) (εTerm l (eval (εTerm l t2)))
    ==. TLabel (εTerm l t1) (εTerm l (eval t2))
        ? εTermIdempotent l t1
        &&& eraseEvalEraseSimulation l t2
    ==. εTerm l (eval t)
    *** QED

eraseEvalEraseSimulation l t@(TLabel t1 t2) =
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TLabel (εTerm l t1) (εTerm l t2)))
    ==. εTerm l (TLabel (eval (εTerm l t1)) (εTerm l t2))
        ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalse l t
    ==. TLabel (εTerm l (eval (εTerm l t1))) (εTerm l (εTerm l t2))
    ==. TLabel (εTerm l (eval t1)) (εTerm l t2)
        ? εTermIdempotent l t2
        &&& eraseEvalEraseSimulation l t1
    ==. εTerm l (eval t)
    *** QED

eraseEvalEraseSimulation l t@(TLabelOf t1') | TLabeledTCB l' t1 <- t1' =
    if  l' `canFlowTo` l then
            εTerm l (eval (εTerm l t))
        ==. εTerm l (eval (TLabelOf (εTerm l (TLabeledTCB l' t1))))
        ==. εTerm l (eval (TLabelOf (TLabeledTCB l' (εTerm l t1))))
        ==. εTerm l (TVLabel l')
            ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalse l t
        ==. εTerm l (eval t)
        *** QED
        
    else
            εTerm l (eval (εTerm l t))
        ==. εTerm l (eval (TLabelOf (εTerm l (TLabeledTCB l' t1))))
        ==. εTerm l (eval (TLabelOf (TLabeledTCB l' THole)))
        ==. εTerm l (TVLabel l')
            ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalse l t
        ==. εTerm l (eval t)
        *** QED

eraseEvalEraseSimulation l t@(TLabelOf t1) =
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TLabelOf (εTerm l t1)))
    ==. εTerm l (TLabelOf (eval (εTerm l t1)))
        ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalse l t
    ==. TLabelOf (εTerm l (eval (εTerm l t1)))
    ==. TLabelOf (εTerm l (eval t1))
        ? eraseEvalEraseSimulation l t1
    ==. εTerm l (eval t)
    *** QED

eraseEvalEraseSimulation l t@(TToLabeled t1 t2) | TVLabel l' <- t1 =
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TToLabeled (εTerm l t1) (εTerm l t2)))
    ==. εTerm l (eval (TToLabeled t1 (εTerm l t2)))
    ==. εTerm l (TToLabeled t1 (εTerm l t2))
        ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalse l t
    ==. TToLabeled (εTerm l t1) (εTerm l (εTerm l t2))
    ==. TToLabeled (εTerm l t1) (εTerm l t2)
        ? εTermIdempotent l t2
    ==. εTerm l (eval t)
    *** QED

eraseEvalEraseSimulation l t@(TToLabeled t1 t2) =
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval (TToLabeled (εTerm l t1) (εTerm l t2)))
    ==. εTerm l (TToLabeled (eval (εTerm l t1)) (εTerm l t2))
        ? propagateExceptionFalseEvalsToNonexception t &&& erasePropagateExceptionFalse l t
    ==. TToLabeled (εTerm l (eval (εTerm l t1))) (εTerm l (εTerm l t2))
    ==. TToLabeled (εTerm l (eval t1)) (εTerm l t2)
        ? εTermIdempotent l t2
        &&& eraseEvalEraseSimulation l t1
    ==. εTerm l (eval t)
    *** QED
    {- 

eraseEvalEraseSimulation l THole = 
        εTerm l (eval (εTerm l THole))
    ==. εTerm l (eval THole)
    *** QED

eraseEvalEraseSimulation l TTrue = 
        εTerm l (eval (εTerm l TTrue))
    ==. εTerm l (eval TTrue)
    *** QED

eraseEvalEraseSimulation l TFalse = 
        εTerm l (eval (εTerm l TFalse))
    ==. εTerm l (eval TFalse)
    *** QED

eraseEvalEraseSimulation l TUnit =
        εTerm l (eval (εTerm l TUnit))
    ==. εTerm l (eval TUnit)
    *** QED

eraseEvalEraseSimulation l (TVar v) =
        εTerm l (eval (εTerm l (TVar v)))
    ==. εTerm l (eval (TVar v))
    *** QED


eraseEvalEraseSimulation l (TVLabel v) =
        εTerm l (eval (εTerm l (TVLabel v)))
    ==. εTerm l (eval (TVLabel v))
    *** QED

eraseEvalEraseSimulation l TException =
        εTerm l (eval (εTerm l TException))
    ==. εTerm l (eval TException)
    *** QED

eraseEvalEraseSimulation l TGetLabel =
        εTerm l (eval (εTerm l TGetLabel))
    ==. εTerm l (eval TGetLabel)
    *** QED

eraseEvalEraseSimulation l TGetClearance =
        εTerm l (eval (εTerm l TGetClearance))
    ==. εTerm l (eval TGetClearance)
    *** QED

eraseEvalEraseSimulation l t = 
        εTerm l (eval (εTerm l t))
    ==. εTerm l (eval t)
    *** QED
-}
   
eraseEvalEraseSimulation l t = undefined


{-
  | TLam {lamVar :: Var, lamTerm :: Term}
  | TBind {tBind1 :: Term, tBind2 :: Term}
  | TLowerClearance Term
  | TLabeledTCB {tLabeledLabel :: Label, tLabeledTerm :: Term}
-}
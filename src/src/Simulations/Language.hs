{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}

module Simulations.Language where

import Label
import Language
import Programs
import MetaFunctions 
import ProofCombinators



-- -- {-@ automatic-instances propagateExceptionFalseNotException @-}
-- {-@ propagateExceptionFalseNotException 
--  :: {t : Term | propagateException t == False}
--  -> {v : Proof | not (t == TException)}
--  @-}
-- -- -> {v : Proof | not (t == TException)} -- JP: This version doesn't work.
-- propagateExceptionFalseNotException :: Term -> Proof
-- propagateExceptionFalseNotException t | propagateException t = unreachable
-- propagateExceptionFalseNotException TException = unreachable -- assert (propagateException TException)
-- -- propagateExceptionFalseNotException (TIf a b c) = trivial -- assertNotEqual (TIf a b c) TException -- trivial -- undefined -- assertNotEqual t TException
-- propagateExceptionFalseNotException _ = trivial

{- automatic-instances propagateExceptionFalseEvalsToNonexception @-}
{-@ propagateExceptionFalseEvalsToNonexception 
 :: {t : Term | not (propagateException t)}
 -> v : {not (eval t == TException)}
 @-}
propagateExceptionFalseEvalsToNonexception :: Term -> Proof
propagateExceptionFalseEvalsToNonexception t | propagateException t = unreachable --  assertEqual (propagateException t) False
propagateExceptionFalseEvalsToNonexception TException = unreachable
-- propagateExceptionFalseEvalsToNonexception t = $wine eval t
propagateExceptionFalseEvalsToNonexception t@(TFix (TLam x t1)) = 
        eval t
    ==! subst (Sub x (TFix (TLam x t1))) t1
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TFix t1) = 
        eval t
    ==! TFix (eval t1)
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TIf TTrue t2 _) = 
        eval t
    ==! t2
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TIf TFalse _ t3) = 
        eval t
    ==! t3
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TIf t1 t2 t3) = 
        eval t
    ==! TIf (eval t1) t2 t3
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TApp (TLam x t1) t2) = 
        eval t
    ==! subst (Sub x t2) t1
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TApp t1 t2) = 
        eval t
    ==! TApp (eval t1) t2
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TJoin (TVLabel l1) (TVLabel l2)) = 
        eval t
    ==! TVLabel (join l1 l2)
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TJoin (TVLabel l1) t2) = 
        eval t
    ==! TJoin (TVLabel l1) (eval t2)
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TJoin t1 t2) = 
        eval t
    ==! TJoin (eval t1) t2
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TMeet (TVLabel l1) (TVLabel l2)) = 
        eval t
    ==! TVLabel (meet l1 l2)
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TMeet (TVLabel l1) t2) = 
        eval t
    ==! TMeet (TVLabel l1) (eval t2)
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TMeet t1 t2) = 
        eval t
    ==! TMeet (eval t1) t2
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TCanFlowTo (TVLabel l1) (TVLabel l2)) = 
        eval t
    ==! boolToTerm (canFlowTo l1 l2)
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TCanFlowTo (TVLabel l1) t2) = 
        eval t
    ==! TCanFlowTo (TVLabel l1) (eval t2)
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TCanFlowTo t1 t2) = 
        eval t
    ==! TCanFlowTo (eval t1) t2
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TLowerClearance t1) = 
        eval t
    ==! TLowerClearance (eval t1)
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TUnlabel t1) = 
        eval t
    ==! TUnlabel (eval t1)
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TLabel l@(TVLabel _) t2) = 
        eval t
    ==! TLabel l (eval t2)
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TLabel t1 t2) = 
        eval t
    ==! TLabel (eval t1) t2
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TLabelOf (TLabeledTCB l _ )) = 
        eval t
    ==! TVLabel l
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TLabelOf t1) = 
        eval t
    ==! TLabelOf (eval t1)
    *** QED

propagateExceptionFalseEvalsToNonexception t@(TToLabeled l@(TVLabel _) t2) = 
        eval t
    ==! TToLabeled l (eval t2)
    *** QED
propagateExceptionFalseEvalsToNonexception t@(TToLabeled t1 t2) = 
        eval t
    ==! TToLabeled (eval t1) t2
    *** QED

propagateExceptionFalseEvalsToNonexception t = -- @(TLam _ _) = 
        eval t
    ==! t
    *** QED

-- propagateExceptionFalseEvalsToNonexception t@(TBind _ _) = 
--         eval t
--     ==! t
--     *** QED
-- 
-- propagateExceptionFalseEvalsToNonexception t@(TLabeledTCB _ _) = 
--         eval t
--     ==! t
--     *** QED
-- 
-- propagateExceptionFalseEvalsToNonexception t@THole = 
--         eval t
--     ==! t
--     *** QED
-- 
-- propagateExceptionFalseEvalsToNonexception t@TTrue = 
--         eval t
--     ==! t
--     *** QED
-- 
-- propagateExceptionFalseEvalsToNonexception t@TFalse = 
--         eval t
--     ==! t
--     *** QED
-- 
-- propagateExceptionFalseEvalsToNonexception t@TUnit = 
--         eval t
--     ==! t
--     *** QED
-- 
-- propagateExceptionFalseEvalsToNonexception t@(TVar _) = 
--         eval t
--     ==! t
--     *** QED
-- 
-- propagateExceptionFalseEvalsToNonexception t@(TVLabel _) = 
--         eval t
--     ==! t
--     *** QED
-- 
-- propagateExceptionFalseEvalsToNonexception t@TGetLabel = 
--         eval t
--     ==! t
--     *** QED
-- 
-- propagateExceptionFalseEvalsToNonexception t@TGetClearance = 
--         eval t
--     ==! t
--     *** QED

-- propagateExceptionFalseEvalsToNonexception t = 
--         eval t
--     ==! t
--     *** QED
-- 
-- propagateExceptionFalseEvalsToNonexception t = 
--         eval t
--     ==! t
--     *** QED

    --(
    --        eval t
    --    ==! t2
    --    -- ==/ TException
    --    *** QED
    --) &&& propagateExceptionFalseNotException t2 
    -- assertEqual (propagateException t2) False &&& propagateExceptionFalseEvalsToNonexception t2 -- &&&  assertNotEqual TException t2
-- -- propagateExceptionFalseEvalsToNonexception t2 -- assert (propagateException t2 == False)
-- propagateExceptionFalseEvalsToNonexception _ = undefined

-- {-@ automatic-instances erasePropagateExceptionFalseEvalsToNonexception @-}
{-@ erasePropagateExceptionFalseEvalsToNonexception
 :: l : Label
 -> {t : Term | not (eval t == TException)}
 -> {v : Proof | not (eval (εTerm l t) == TException)}
 @-}
erasePropagateExceptionFalseEvalsToNonexception :: Label -> Term -> Proof
erasePropagateExceptionFalseEvalsToNonexception _ _ = undefined

{-@ erasePropagateExceptionTrueEvalsToException
 :: l : Label
 -> {t : Term | eval t == TException}
 -> {v : Proof | eval (εTerm l t) == TException}
 @-}
erasePropagateExceptionTrueEvalsToException :: Label -> Term -> Proof
erasePropagateExceptionTrueEvalsToException _ _ = undefined


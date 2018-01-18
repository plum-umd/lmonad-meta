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

{-@ automatic-instances propagateExceptionFalseEvalsToNonexception @-}
{-@ propagateExceptionFalseEvalsToNonexception 
 :: {t : Term | not (propagateException t)}
 -> v : {not (eval t == TException)}
 @-}
propagateExceptionFalseEvalsToNonexception :: Term -> Proof
propagateExceptionFalseEvalsToNonexception t | propagateException t 
  = unreachable --  assertEqual (propagateException t) False
propagateExceptionFalseEvalsToNonexception TException 
  = unreachable
propagateExceptionFalseEvalsToNonexception (TFix (TLam _ _)) 
  = trivial 
propagateExceptionFalseEvalsToNonexception (TFix _) 
  = trivial
propagateExceptionFalseEvalsToNonexception (TIf TTrue _ _)
  = trivial
propagateExceptionFalseEvalsToNonexception (TIf TFalse _ _)
  = trivial
propagateExceptionFalseEvalsToNonexception (TIf _ _ _)
  = trivial
propagateExceptionFalseEvalsToNonexception (TApp (TLam _ _) _)
  = trivial
propagateExceptionFalseEvalsToNonexception (TApp _ _)
  = trivial
propagateExceptionFalseEvalsToNonexception (TJoin (TVLabel _) (TVLabel _))
  = trivial
propagateExceptionFalseEvalsToNonexception (TJoin (TVLabel _) _)
  = trivial
propagateExceptionFalseEvalsToNonexception (TJoin _ _)
  = trivial
propagateExceptionFalseEvalsToNonexception (TMeet (TVLabel _) (TVLabel _))
  = trivial
propagateExceptionFalseEvalsToNonexception (TMeet (TVLabel _) _)
  = trivial
propagateExceptionFalseEvalsToNonexception (TMeet _ _)
  = trivial
propagateExceptionFalseEvalsToNonexception (TCanFlowTo (TVLabel _) (TVLabel _))
  = trivial
propagateExceptionFalseEvalsToNonexception (TCanFlowTo (TVLabel _) _)
  = trivial
propagateExceptionFalseEvalsToNonexception (TCanFlowTo _ _)
  = trivial
propagateExceptionFalseEvalsToNonexception (TLowerClearance _)
  = trivial
propagateExceptionFalseEvalsToNonexception (TUnlabel _)
  = trivial
propagateExceptionFalseEvalsToNonexception (TLabel (TVLabel _) _)
  = trivial
propagateExceptionFalseEvalsToNonexception (TLabel _ _)
  = trivial
propagateExceptionFalseEvalsToNonexception (TLabelOf (TLabeledTCB _ _ ))
  = trivial
propagateExceptionFalseEvalsToNonexception (TLabelOf _)
  = trivial
propagateExceptionFalseEvalsToNonexception (TToLabeled (TVLabel _) _)
  = trivial
propagateExceptionFalseEvalsToNonexception (TToLabeled _ _)
  = trivial
propagateExceptionFalseEvalsToNonexception _
  = trivial


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
 -> {t : Term | eval t /= TException}
 -> {v : Proof | eval (εTerm l t) /= TException}
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


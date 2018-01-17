{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}
{-@ LIQUID "--automatic-instances=liquidinstanceslocal" @-}

module Simulations.Language where

import Label
import Language
import Programs
import MetaFunctions 
import ProofCombinators



-- {-@ automatic-instances propagateExceptionFalseNotException @-}
{-@ propagateExceptionFalseNotException 
 :: {t : Term | not (propagateException t)}
 -> {v : Proof | t /= TException}
 @-}
-- -> {v : Proof | t /= TException} -- JP: This version doesn't work.
propagateExceptionFalseNotException :: Term -> Proof
propagateExceptionFalseNotException t | propagateException t = unreachable
propagateExceptionFalseNotException TException = unreachable -- assert (propagateException TException)
-- propagateExceptionFalseNotException (TIf a b c) = trivial -- assertNotEqual (TIf a b c) TException -- trivial -- undefined -- assertNotEqual t TException
propagateExceptionFalseNotException _ = trivial

-- {-@ automatic-instances propagateExceptionFalseEvalsToNonexception @-}
{-@ propagateExceptionFalseEvalsToNonexception 
 :: {t : Term | propagateException t == False}
 -> v : {not (eval t == TException)}
 @-}
propagateExceptionFalseEvalsToNonexception :: Term -> Proof
propagateExceptionFalseEvalsToNonexception t | propagateException t = unreachable --  assertEqual (propagateException t) False
propagateExceptionFalseEvalsToNonexception TException = unreachable
-- propagateExceptionFalseEvalsToNonexception (TFix _) = undefined -- trivial
propagateExceptionFalseEvalsToNonexception t@(TIf TTrue t2 _) = undefined
    --(
    --        eval t
    --    ==! t2
    --    -- ==/ TException
    --    *** QED
    --) &&& propagateExceptionFalseNotException t2 
    -- assertEqual (propagateException t2) False &&& propagateExceptionFalseEvalsToNonexception t2 -- &&&  assertNotEqual TException t2
-- -- propagateExceptionFalseEvalsToNonexception t2 -- assert (propagateException t2 == False)
propagateExceptionFalseEvalsToNonexception _ = undefined

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


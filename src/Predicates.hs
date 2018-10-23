module Predicates where

data Pred = Pred { pDependOn1 :: Bool, pDependOn2 :: Bool, pValue :: Bool}
  deriving Eq 


{-@ measure Predicates.pDependOn1 :: Pred -> Bool @-}
{-@ measure Predicates.pDependOn2 :: Pred -> Bool @-}
{-@ measure Predicates.pValue     :: Pred -> Bool @-}
{-@ measure Predicates.evalPredicate :: Pred -> a -> Bool @-}

{-@ pDependOn1 :: p:Pred -> {b:Bool | b == pDependOn1 p} @-}
{-@ pDependOn2 :: p:Pred -> {b:Bool | b == pDependOn2 p} @-}
{-@ pValue     :: p:Pred -> {b:Bool | b == pValue p} @-}

{-@ assume evalPredicate :: p:Pred -> x:a -> {v:Bool | v == Predicates.evalPredicate p x } @-} 
evalPredicate :: Pred -> a -> Bool 
evalPredicate p _ = pValue p   


{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}

module Determinacy where

-- import Language.Haskell.Liquid.ProofCombinators

import Label
import Language 
import Programs 
import MetaFunctions 
import ProofCombinators

_hackImport  :: Term 
_hackImport = THole 

{-@ determinacy :: l:Label -> k:Program -> k1:Program -> k2:Program 
       -> {v:Proof | evalEraseProgram k l == k1 && evalEraseProgram k l == k2} 
       -> {k1 == k2 } @-}
determinacy :: Label -> Program -> Program -> Program -> Proof -> Proof
determinacy l k k1 k2 _  
  =   evalEraseProgram k l 
  ==. k1
  ==. k2 
  *** QED

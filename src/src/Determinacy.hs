{-@ determinacy :: l:Label -> k:Program -> k1:Program -> k2:Program -> n1:Index -> n2:Index
       -> {v:Proof | evalEraseProgram k l == Pair n1 k1 && evalEraseProgram k l == Pair n2 k2} 
       -> {k1 == k2 && n1 == n2} @-}
determinacy :: Label -> Program -> Program -> Program -> Index -> Index -> Proof -> Proof
determinacy l k k1 k2 n1 n2 _  
  =   evalEraseProgram k l 
  ==. Pair n1 k1
  ==. Pair n2 k2 
  *** QED
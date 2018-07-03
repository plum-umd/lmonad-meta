{-@ LIQUID "--reflection"  @-}

module NonInterference where
import Prelude hiding (Maybe(..), fromJust, isJust)

import ProofCombinators
import Simulations.Simulations 
import Labels 
import Programs 

{-@ 
nonInterference
   :: Label l => l:l  
   -> p1:{Program l  | terminates p1 && ς p1 } 
   -> p2:{Program l  | terminates p2 && ς p2 }
   -> {v:Proof       | ε l p1 == ε l p2}
   -> p1':{Program l | eval p1 == p1' } 
   -> p2':{Program l | eval p2 == p2' } 
   -> {v:Proof       | ε l p1' == ε l p2'}  
 @-}

nonInterference
   :: (Label l, Eq l) => l 
   -> Program l -> Program l -> Proof
   -> Program l -> Program l
   -> Proof  
nonInterference l p1 p2 equivProp p1' p2' 
  =   ε l p1'
  ==. ε l (eval p1)
  ==. ε l (eval (ε l p1)) ? simulations l p1 
  ==. ε l (eval (ε l p2)) ? equivProp
  ==. ε l (eval p2)       ? simulations l p2 
  ==. ε l p2' 
  *** QED 

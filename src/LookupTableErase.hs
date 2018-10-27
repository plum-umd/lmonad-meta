{-@ LIQUID "--reflection"  @-}
module LookupTableErase where

import Labels 
import Prelude hiding (Maybe(..), fromJust, isJust)
import Programs 

import ProofCombinators 


lookupTableErase :: (Eq l, Label l) => l -> TName -> DB l -> Proof 
{-@ lookupTableErase :: Label l => l:l -> n:TName -> db:DB l 
  -> { (isJust (lookupTable n db) <=> isJust (lookupTable n (εDB l db))) 
  && (isJust (lookupTable n db) => 
      (tableInfo (fromJust (lookupTable n db)) == tableInfo (fromJust (lookupTable n (εDB l db))))) } @-}
lookupTableErase l n [] 
  =   isJust (lookupTable n (εDB l []))
  *** QED 

lookupTableErase l n ((Pair n' t):ts)
  | n == n' 
  =   isJust (lookupTable n (εDB l ((Pair n' t):ts)))
  ==. isJust (lookupTable n (Pair n' (εTable l t):εDB l ts))
  ==. isJust (Just (εTable l t))
  ==. isJust (Just t) 
  ==. isJust (lookupTable n ((Pair n' t):ts)) 
  *** QED   

lookupTableErase l n ((Pair n' t):ts)
  =   isJust (lookupTable n (εDB l ((Pair n' t):ts)))
  ==. isJust (lookupTable n (Pair n' (εTable l t):εDB l ts))
  ==. isJust (lookupTable n (εDB l ts))
      ? lookupTableErase l n ts 
  ==. isJust (lookupTable n ts) 
  ==. isJust (lookupTable n ((Pair n' t):ts)) 
  *** QED     
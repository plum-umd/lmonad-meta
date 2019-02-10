{-@ LIQUID "--reflection"  @-}
module EraseTableAnyNothingJust where

import Labels 
import Predicates 
import Prelude hiding (Maybe(..), fromJust, isJust)
import Programs 

import ProofCombinators 


{-@ εTableAnyNothingJust
  :: (Label l, Eq l) 
  => l:l 
  -> n:TName 
  -> db:{DB l |  (isJust (lookupTable n db)) && not (canFlowTo (tableLabel (tableInfo (fromJust (lookupTable n db)))) l)}
  -> p:Pred -> v2:SDBTerm l
  -> {εDB l (updateDBNothingJust db n p v2) == εDB l db }
@-}

εTableAnyNothingJust :: (Eq l, Label l) => l -> TName -> DB l -> Pred -> Term l -> Proof 
εTableAnyNothingJust l n [] p v2
  =   εDB l (updateDBNothingJust [] n p v2) 
  ==. εDB l []
  *** QED  

εTableAnyNothingJust l n db@((Pair n' t@(Table ti rs)):ts) p v2
  | n == n'
  =   tableInfo (fromJust (lookupTable n ((Pair n' (Table ti rs)):ts)))
  ==. tableInfo (fromJust (Just (Table ti rs)))
  ==. ti *** QED 
      ? assert (not (tableLabel ti `canFlowTo` l))
      ? (εDB l (updateDBNothingJust db n p v2)
  ==. εDB l (Pair n (Table ti (updateRowsNothingJust p v2 rs)):ts) 
  ==. Pair n (εTable l (Table ti (updateRowsNothingJust p v2 rs))):εDB l ts 
  ==. Pair n (Table ti []):εDB l ts 
  ==. Pair n (εTable l (Table ti rs)):εDB l ts 
  ==. εDB l db
  *** QED )

εTableAnyNothingJust l n db@((Pair n' t):ts) p v2
  =  (tableInfo (fromJust (lookupTable n ((Pair n' t):ts)))
  ==. tableInfo (fromJust (lookupTable n ts))
  *** QED )
  ? ( εDB l (updateDBNothingJust db n p v2)
  ==. εDB l (Pair n' t: updateDBNothingJust ts n p v2) 
  ==. Pair n' (εTable l t):εDB l (updateDBNothingJust ts n p v2)
      ? εTableAnyNothingJust l n ts p v2
  ==. Pair n' (εTable l t):εDB l ts 
  ==. εDB l ((Pair n' t):ts)
  *** QED ) 

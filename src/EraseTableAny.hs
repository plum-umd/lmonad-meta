{-@ LIQUID "--reflection"  @-}
module EraseTableAny where

import Labels 
import Prelude hiding (Maybe(..), fromJust, isJust)
import Programs 

import ProofCombinators 


{-@ εTableAny 
  :: (Label l, Eq l) 
  => l:l 
  -> n:TName 
  -> db:{DB l |  (Programs.isJust (lookupTable n db)) && not (canFlowTo (tableLabel (tableInfo (Programs.fromJust (lookupTable n db)))) l)}
  -> p:Pred l -> v1:{t:Term l | isDBValue t && ςTerm t } -> v2:{t:Term l | isDBValue t && ςTerm t }
  -> {εDB l (updateDB db n p v1 v2) == εDB l db }
@-}

εTableAny :: (Eq l, Label l) => l -> TName -> DB l -> Pred l -> Term l -> Term l -> Proof 
εTableAny l n [] p v1 v2
  =   εDB l (updateDB [] n p v1 v2) 
  ==. εDB l []
  *** QED  

εTableAny l n db@((Pair n' t@(Table ti rs)):ts) p v1 v2
  | n == n'
  =   tableInfo (fromJust (lookupTable n ((Pair n' (Table ti rs)):ts)))
  ==. tableInfo (fromJust (Just (Table ti rs)))
  ==. ti *** QED 
      ? assert (not (tableLabel ti `canFlowTo` l))
      ? (εDB l (updateDB db n p v1 v2)
  ==. εDB l (Pair n (Table ti (updateRows p v1 v2 rs)):ts) 
  ==. Pair n (εTable l (Table ti (updateRows p v1 v2 rs))):εDB l ts 
  ==. Pair n (Table ti []):εDB l ts 
  ==. Pair n (εTable l (Table ti rs)):εDB l ts 
  ==. εDB l db
  *** QED )

εTableAny l n db@((Pair n' t):ts) p v1 v2
  =  (tableInfo (fromJust (lookupTable n ((Pair n' t):ts)))
  ==. tableInfo (fromJust (lookupTable n ts))
  *** QED )
  ? ( εDB l (updateDB db n p v1 v2)
  ==. εDB l (Pair n' t: updateDB ts n p v1 v2) 
  ==. Pair n' (εTable l t):εDB l (updateDB ts n p v1 v2)
      ? εTableAny l n ts p v1 v2
  ==. Pair n' (εTable l t):εDB l ts 
  ==. εDB l ((Pair n' t):ts)
  *** QED ) 

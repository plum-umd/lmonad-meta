{-@ LIQUID "--reflection"  @-}
module Simulations.UpdateOneNothingJust where

import ProofCombinators
import Labels 
import Programs 
import Predicates 

import Idempotence 
import LabelUpdateCheckNothingJust
import Simulations.Terms

import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsUpdateOneNothingJust
  :: Label l => l:l -> lc:{l | canFlowTo lc l } 
  -> db:DB l 
  -> n:{TName | isJust (lookupTable n db) && isJust (lookupTable n (εDB l db))}
  -> p:Pred
  -> l2:l  
  -> v2:SDBTerm l 
  -> t:{Table l | not (canFlowTo (field1Label (tableInfo t)) l ) && (Just t == lookupTable n db) && (updateLabelCheckNothingJust lc t p l2 v2)  } 
  -> εt:{Table l | (Just εt == lookupTable n (εDB l db)) && not (updateLabelCheckNothingJust lc εt p l2 (if (canFlowTo l2 l) then v2 else THole)) } 
  -> { εDB l db == εDB l (updateDBNothingJust db n p v2) } @-}

simulationsUpdateOneNothingJust :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> l -> Term l -> Table l -> Table l  -> Proof
simulationsUpdateOneNothingJust l lc [] n p l2 v2 _ _
  =   εDB l [] 
  ==. εDB l (updateDBNothingJust [] n p v2) 
  *** QED 

simulationsUpdateOneNothingJust l lc ((Pair n' t@(Table ti rs)):ts) n p  l2 v2 t' εt'
  | n == n' && (tableLabel ti `canFlowTo` l)
  =   (Just t' ==. 
      lookupTable n ((Pair n' (Table ti rs)):ts) ==. 
      Just t 
      *** QED)
  &&& (Just εt' ==. 
      lookupTable n (εDB l ((Pair n' (Table ti rs)):ts)) ==. 
      lookupTable n (Pair n' (εTable l (Table ti rs)):εDB l ts) ==. 
      Just (εTable l t) 
      *** QED)
  &&& ( εt' ==. 
        εTable l (Table ti rs) ==. 
        Table ti (εRows l ti rs) *** QED 
      )
  &&& (εDB l (updateDBNothingJust (Pair n' t:ts) n p v2)
  ==. εDB l (Pair n' (Table ti (updateRowsNothingJust p v2 rs)):ts)
  ==. Pair n' (εTable l (Table ti (updateRowsNothingJust p v2 rs))) : εDB l ts
  ==. Pair n' (Table ti (εRows l ti (updateRowsNothingJust p v2 rs))):εDB l ts
      ? use (εRows l ti (updateRowsNothingJust p v2 rs) == εRows l ti rs)
      ? use (updateLabelCheckNothingJust lc t p l2 v2)
      ? use (updateRowsCheckNothingJust lc lφ ti p l2 v2 rs)
      ? use (not (updateLabelCheckNothingJust lc εt' p l2 εv2))
      ? use (not (updateRowsCheckNothingJust lc (lfTable p εt') ti p l2 εv2 (εRows l ti rs)))
      ? use (canFlowTo (lfRows p ti rs) lφ)
      ? simulationsUpdateRowsNothingJust l lc lφ εlφ ti p l2 v2 rs      
      ? use (canFlowTo (lfRows p ti (εRows l ti rs)) εlφ)
  ==. Pair n' (Table ti (εRows l ti rs)):εDB l ts 
  ==. Pair n' (εTable l (Table ti rs)):εDB l ts     
  ==. εDB l (Pair n' (Table ti rs):ts)
  *** QED)
  | n == n' && not (tableLabel ti `canFlowTo` l)
  =   εDB l (updateDBNothingJust (Pair n' t:ts) n p v2)
  ==. εDB l (Pair n' (Table ti (updateRowsNothingJust p v2 rs)):ts) 
  ==. Pair n' (εTable l (Table ti (updateRowsNothingJust p v2 rs))):εDB l ts
  ==. Pair n' (Table ti []):εDB l ts 
  ==. Pair n' (εTable l (Table ti rs)):εDB l ts 
  ==. εDB l (Pair n' (Table ti rs):ts)
  *** QED 
  | n /= n' 
  =  (Just t' ==. 
      lookupTable n ((Pair n' (Table ti rs)):ts) ==. 
      Just t 
      *** QED)
  &&& (Just εt' ==. 
      lookupTable n (εDB l ((Pair n' (Table ti rs)):ts)) ==. 
      lookupTable n (Pair n' (εTable l (Table ti rs)):εDB l ts) ==. 
      Just (εTable l t) 
      *** QED)
  &&& (εDB l (updateDBNothingJust (Pair n' t:ts) n p v2)
  ==.  εDB l (Pair n' (Table ti rs): updateDBNothingJust ts n p v2)
  ==.  Pair n' (εTable l (Table ti rs)):εDB l (updateDBNothingJust ts n p v2)
      ? simulationsUpdateOneNothingJust l lc ts n p l2 v2 t' εt'
      ? use (εDB l (updateDBNothingJust ts n p v2) == εDB l ts)
  ==. Pair n' (εTable l (Table ti rs)):εDB l ts
  ==. εDB l (Pair n' (Table ti rs):ts) 
  *** QED) 
  
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole
    lφ  = lawFlowReflexivity (lfRows p ti rs) `cast` lfTable p (Table ti rs)
    εlφ = lawFlowReflexivity (lfRows p ti (εRows l ti rs)) `cast` lfTable p (Table ti (εRows l ti rs))



{-@ simulationsUpdateRowsNothingJust
  :: (Label l, Eq l)
  => l:l -> lc:{l | canFlowTo lc l } 
  -> lf:l -> elf:l 
  -> ti: {TInfo l | not (canFlowTo (field1Label ti) l) }
  -> p:Pred
  -> l2:l 
  -> v2: SDBTerm l 
  -> rs: [Row l] 
  -> { εRows l ti rs = εRows l ti (updateRowsNothingJust p v2 rs) } / [len rs] @-}
simulationsUpdateRowsNothingJust
  :: (Label l, Eq l)
  => l -> l -> l -> l -> TInfo l -> Pred -> l -> Term l -> [Row l] -> Proof 
simulationsUpdateRowsNothingJust l lc _ _ ti p l2 v2 []
  =   εRows l ti (updateRowsNothingJust p v2 [])
  ==. εRows l ti []
  *** QED   
simulationsUpdateRowsNothingJust l lc lφ εlφ ti p l2 v2 (r:rs) 
  =   εRows l ti (updateRowsNothingJust p v2 (r:rs))
  ==. εRows l ti (updateRowNothingJust p v2 r:updateRowsNothingJust p v2 rs)
  ==. εRow l ti (updateRowNothingJust p v2 r):εRows l ti (updateRowsNothingJust p v2 rs)
      ? simulationsUpdateRowNothingJust l lc ti p l2 v2 r
      ? simulationsUpdateRowsNothingJust l lc lφ εlφ ti p l2 v2 rs

  ==. εRow  l ti r:εRows l ti rs
  ==. εRows l ti (r:rs)
  *** QED  
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole



{-@ simulationsUpdateRowNothingJust
  :: (Label l, Eq l)
  => l:l -> lc:{l | canFlowTo lc l } 
  -> ti: {TInfo l | not (canFlowTo (field1Label ti) l) }
  -> p:Pred
  -> l2:l 
  -> v2: SDBTerm l 
  -> r: Row l
  -> { εRow l ti r = εRow l ti (updateRowNothingJust p v2 r) } @-}
simulationsUpdateRowNothingJust :: (Label l, Eq l) =>
  l -> l -> TInfo l -> Pred -> l -> Term l -> Row l -> Proof

simulationsUpdateRowNothingJust  l lc ti p l2 v2 r@(Row k o1 o2)
  =   εRow l ti r
  ==. Row k THole THole
  ==. εRow l ti (updateRowNothingJust p v2 r)
  *** QED




{-@ simulationsUpdateOneErasedNothingJust
  :: Label l => l:l -> lc:{l | canFlowTo lc l } 
  -> db:DB l 
  -> n:{TName | isJust (lookupTable n db) && isJust (lookupTable n (εDB l db))}
  -> p:Pred
  -> l2:l  
  -> v2:SDBTerm l 
  -> t:{Table l  | (not (canFlowTo (field1Label (tableInfo t)) l)) && (Just t == lookupTable n db) && not (updateLabelCheckNothingJust lc t p l2 v2) } 
  -> εt:{Table l | (Just εt == lookupTable n (εDB l db)) && (updateLabelCheckNothingJust lc εt p  l2 (if (canFlowTo l2 l) then v2 else THole)) } 
  -> { εDB l (updateDBNothingJust (εDB l db) n p  (if (canFlowTo l2 l) then v2 else THole)) == εDB l db } @-}
simulationsUpdateOneErasedNothingJust :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> l -> Term l -> Table l -> Table l -> Proof
simulationsUpdateOneErasedNothingJust l lc [] n p l2 v2 _ _ 
  =   εDB l [] 
  ==. εDB l (updateDBNothingJust (εDB l []) n p εv2) 
  *** QED 
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole

simulationsUpdateOneErasedNothingJust l lc ((Pair n' t@(Table ti rs)):ts) n p l2 v2 t' εt'
  | n == n' && not (tableLabel ti `canFlowTo` l)
  =   εDB l (updateDBNothingJust (εDB l ((Pair n' t):ts)) n p εv2)
  ==. εDB l (updateDBNothingJust ((Pair n' (εTable l t)):εDB l ts) n p εv2)
  ==. εDB l (updateDBNothingJust ((Pair n' (εTable l (Table ti rs))):εDB l ts) n p εv2)
  ==. εDB l (updateDBNothingJust ((Pair n' (Table ti [])):εDB l ts) n p εv2)
  ==. εDB l (Pair n' (Table ti (updateRowsNothingJust p εv2 [])):εDB l ts)
  ==. Pair n' (εTable l (Table ti [])):(εDB l (εDB l ts))
      ?  εDBIdempotent l ts 
  ==. Pair n' (Table ti []):εDB l ts 
  ==. Pair n' (εTable l (Table ti rs)):εDB l ts 
  ==. εDB l (Pair n' (Table ti rs):ts) 
  *** QED
  | n == n' && tableLabel ti `canFlowTo` l
  =  (Just t' ==. 
      lookupTable n ((Pair n' (Table ti rs)):ts) ==. 
      Just t 
      *** QED)
  &&& (Just εt' ==. 
      lookupTable n (εDB l ((Pair n' (Table ti rs)):ts)) ==. 
      lookupTable n (Pair n' (εTable l (Table ti rs)):εDB l ts) ==. 
      Just (εTable l t) 
      *** QED)
  &&& ( εt' ==. 
        εTable l (Table ti rs) ==. 
        Table ti (εRows l ti rs) *** QED 
      )
  &&& (εDB l (updateDBNothingJust (εDB l ((Pair n' t):ts)) n p εv2)
  ==.  εDB l (updateDBNothingJust ((Pair n' (εTable l t)):εDB l ts) n p εv2)
  ==.  εDB l (updateDBNothingJust ((Pair n' (εTable l (Table ti rs))):εDB l ts) n p εv2)
  ==.  εDB l (updateDBNothingJust ((Pair n' (Table ti (εRows l ti rs))):εDB l ts) n p εv2)
  ==.  εDB l (Pair n' (Table ti (updateRowsNothingJust p εv2 (εRows l ti rs))):εDB l ts) 
  ==.  Pair n' (εTable l (Table ti (updateRowsNothingJust p εv2 (εRows l ti rs)))):εDB l (εDB l ts)
  ==.  Pair n' (Table ti (εRows l ti (updateRowsNothingJust p εv2 (εRows l ti rs)))):εDB l (εDB l ts)
      ? use (not (updateLabelCheckNothingJust lc t p l2 v2))
      ? use (not (updateRowsCheckNothingJust lc lφ ti p l2 v2 rs))
      ? use (updateLabelCheckNothingJust lc εt' p l2 εv2)
      ? use (updateRowsCheckNothingJust lc (lfTable p εt') ti p l2 εv2 (εRows l ti rs))
      ? use (canFlowTo (lfRows p ti (εRows l ti rs)) εlφ)
      ? simulationsUpdateRowsNothingJust l lc lφ εlφ ti p l2 εv2 (εRows l ti rs)
  ==. Pair n' (Table ti (εRows l ti (εRows l ti rs))):εDB l (εDB l ts)
      ? εRowsIdempotent l ti rs
      ? εDBIdempotent l ts
  ==. Pair n' (Table ti (εRows l ti rs)):εDB l ts 
  ==. Pair n' (εTable l (Table ti rs)):εDB l ts 
  ==. εDB l (Pair n' (Table ti rs):ts)
  *** QED) 

  | n /= n' 
  =  (Just t' ==. 
      lookupTable n ((Pair n' (Table ti rs)):ts) ==. 
      Just t 
      *** QED)
  &&& (Just εt' ==. 
      lookupTable n (εDB l ((Pair n' (Table ti rs)):ts)) ==. 
      lookupTable n (Pair n' (εTable l (Table ti rs)):εDB l ts) ==. 
      Just (εTable l t) 
      *** QED)
  &&& (εDB l (updateDBNothingJust (εDB l ((Pair n' t):ts)) n p εv2)
  ==.  εDB l (updateDBNothingJust ((Pair n' (εTable l t)):εDB l ts) n p εv2)
  ==.  εDB l (Pair n' (εTable l (Table ti rs)): updateDBNothingJust (εDB l ts) n p εv2)
  ==.  Pair n' (εTable l (εTable l (Table ti rs))):εDB l (updateDBNothingJust (εDB l ts) n p εv2)
      ? simulationsUpdateOneErasedNothingJust l lc ts n p l2 v2 t' εt'
      ? use (εDB l (updateDBNothingJust (εDB l ts) n p εv2) == εDB l ts)
      ? εTableIdempotent l (Table ti rs)
  ==. Pair n' (εTable l (Table ti rs)):εDB l ts
  ==. εDB l (Pair n' (Table ti rs):ts) 
  *** QED) 

  where
    εv2 = if (canFlowTo l2 l) then v2 else THole
    lφ  = lawFlowReflexivity (lfRows p ti rs) `cast` lfTable p (Table ti rs)
    εlφ = lawFlowReflexivity (lfRows p ti (εRows l ti rs)) `cast` lfTable p (Table ti (εRows l ti rs))




-- {-@ simulationsUpdateRowsErasedNothingJust
--   :: (Label l, Eq l)
--   => l:l -> lc:{l | canFlowTo lc l } 
--   -> lf:l -> elf:l 
--   -> ti: {TInfo l | not (canFlowTo (field1Label ti) l) }
--   -> p:Pred
--   -> l2:l 
--   -> v2: SDBTerm l 
--   -> rs: [Row l] 
--   -> { εRows l ti rs = εRows l ti (updateRowsNothingJust p v2 (εRows l ti rs)) } / [len rs] @-}
-- simulationsUpdateRowsErasedNothingJust
--   :: (Label l, Eq l)
--   => l -> l -> l -> l -> TInfo l -> Pred -> l -> Term l -> [Row l] -> Proof 
-- simulationsUpdateRowsErasedNothingJust l lc _ _ ti p l2 v2 []
--   =   εRows l ti (updateRowsNothingJust p v2 (εRows l ti []))
--   ==. εRows l ti (updateRowsNothingJust p v2 [])
--   ==. εRows l ti []
--   *** QED   
-- simulationsUpdateRowsErasedNothingJust l lc lφ εlφ ti p l2 v2 (r:rs)

--   ==. 
--   ==. εRows l ti (updateRowNothingJust p v2 r:updateRowsNothingJust p v2 rs)
--   ==. εRow l ti (updateRowNothingJust p v2 r):εRows l ti (updateRowsNothingJust p v2 rs)
--       ? simulationsUpdateRowNothingJust l lc ti p l2 v2 r
--       ? simulationsUpdateRowsNothingJust l lc lφ εlφ ti p l2 v2 rs

--   ==. εRow  l ti r:εRows l ti rs
--   ==. εRows l ti (r:rs)
--   *** QED  
--   where
--     εv2 = if (canFlowTo l2 l) then v2 else THole

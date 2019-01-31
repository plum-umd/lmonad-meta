{-@ LIQUID "--reflection"  @-}

module Simulations.Update where --  (simulationsUpdate) where

import ProofCombinators
import Labels 
import Programs 
import Predicates 

import Idempotence 
import Simulations.Terms 

import Prelude hiding (Maybe(..), fromJust, isJust)
{-@ simulationsUpdatev2  
  :: Label l => l:l -> lc:{l | canFlowTo lc l } 
  -> db:DB l 
  -> n:{TName | isJust (lookupTable n db) }
  -> p:Pred
  -> l2:l  
  -> v2:SDBTerm l 
  -> t: {Table l | (Just t == lookupTable n db) && (updateLabelCheckv2 lc t p l2 v2)}
  -> εt:{Table l | (Just εt == lookupTable n (εDB l db)) &&
                   (updateLabelCheckv2 lc εt p l2 (if (canFlowTo l2 l) then v2 else THole)) } 
  -> { εDB l (updateDBv2 (εDB l db) n p (if (canFlowTo l2 l) then v2 else THole)) == εDB l (updateDBv2 db n p v2) } @-}

simulationsUpdatev2 :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred -> l -> Term l -> Table l -> Table l  -> Proof
simulationsUpdatev2 l lc [] n p l2 v2 _ _
  =   εDB l (updateDBv2 [] n p v2) 
  ==. εDB l [] 
  ==. εDB l (updateDBv2 (εDB l []) n p εv2) 
  *** QED 
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole

    -- is this file needed at all?
simulationsUpdatev2 l lc ((Pair n' t@(Table ti rs)):ts) n p l2 v2 t' εt'
  | n == n' && not (tableLabel ti `canFlowTo` l)
  =   εDB l (updateDBv2 (εDB l ((Pair n' t):ts)) n p εv2)
  ==. εDB l (updateDBv2 (Pair n' (εTable l t): εDB l ts) n p εv2)
  ==. εDB l (updateDBv2 (Pair n' (Table ti []): εDB l ts) n p εv2)
  ==. εDB l (Pair n' (Table ti (updateRowsv2 p εv2 [])): εDB l ts)
  ==. εDB l (Pair n' (Table ti []): εDB l ts)
  ==. Pair n' (εTable l (Table ti [])) : εDB l (εDB l ts)
      ? εDBIdempotent l ts
  ==. Pair n' (Table ti []) : εDB l ts
  ==. Pair n' (εTable l (Table ti (updateRowsv2 p v2 rs))):εDB l ts
  ==. εDB l (Pair n' (Table ti (updateRowsv2 p v2 rs)):ts)
  ==. εDB l (updateDBv2 (Pair n' t:ts) n p v2)
  *** QED
  | n == n' && tableLabel ti `canFlowTo` l
  -- Not sure why the two short proofs are needed, but copied over anyways
  =   (Just t' ==. 
      lookupTable n ((Pair n' (Table ti rs)):ts) ==. 
      Just t 
      *** QED)
  &&& (Just εt' ==. 
      lookupTable n (εDB l ((Pair n' (Table ti rs)):ts)) ==. 
      lookupTable n (Pair n' (εTable l (Table ti rs)):εDB l ts) ==. 
      Just (εTable l t) 
      *** QED)
  &&& (εDB l (updateDBv2 (εDB l ((Pair n' t):ts)) n p εv2)
  ==.  _
  ***  QED)
  where
    εv2 = if (canFlowTo l2 l) then v2 else THole

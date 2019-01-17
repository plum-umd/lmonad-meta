{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"  @-}
module DBValueErase where

import Labels 
import Prelude hiding (Maybe(..), fromJust, isJust)
import Programs 

import ProofCombinators 

{-@ ple dbValueErase @-}
-- {-@ reflect dbValueErase @-}
dbValueErase :: (Label l, Eq l) => l -> Term l -> Proof 
{-@ dbValueErase 
  :: (Label l, Eq l) 
  => l:l 
  -> t:Term l 
  -> { (isDBValue t => εTerm l t == t) && (isDBValue (εTerm l t) =>  isDBValue t) }
  @-} 
dbValueErase l t@(TInt _) 
  = ()
dbValueErase l t@TUnit 
  = ()
dbValueErase l t@TTrue 
  = ()
dbValueErase l t@TFalse 
  = ()
dbValueErase l t@THole 
  = ()
dbValueErase l t@TNil 
  = ()
dbValueErase l t@TNothing
  = ()
dbValueErase l t@(TVLabel _) 
  = ()
dbValueErase l (TCons t1 t2) 
  =   dbValueErase l t1 
  &&& dbValueErase l t2 
dbValueErase l (TJust t)
  =   dbValueErase l t
dbValueErase l t 
  = assert (not (isDBValue t)) 


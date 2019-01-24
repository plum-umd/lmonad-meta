{-@ LIQUID "--reflection"  @-}

module SafeDBValues where

import ProofCombinators 
import Programs
import Labels 
import Prelude hiding (Maybe(..), fromJust, isJust)


{-@ safeDBValue 
  :: (Eq l, Label l) 
  => t:Term l 
  -> { isDBValue t => ςTerm t } @-}  
safeDBValue  :: (Eq l, Label l) => Term l -> Proof 
safeDBValue t@(TInt _) 
  = assert (isDBValue t) &&& assert (ςTerm t)
safeDBValue t@TUnit 
  = assert (isDBValue t) &&& assert (ςTerm t)
safeDBValue t@TTrue 
  = assert (isDBValue t) &&& assert (ςTerm t)
safeDBValue t@TFalse 
  = assert (isDBValue t) &&& assert (ςTerm t)
safeDBValue t@(TVLabel _) 
  = assert (isDBValue t) &&& assert (ςTerm t)
safeDBValue t@TNil 
  = assert (isDBValue t) &&& assert (ςTerm t)
safeDBValue t@TNothing
  = assert (isDBValue t) &&& assert (ςTerm t)

safeDBValue t@(TJust t1) | isDBValue t
  = assert (isDBValue t)
  ? assert (isDBValue t1)
  ? safeDBValue t1
  ? assert (ςTerm t1)
  ? assert (ςTerm t)

safeDBValue t@(TCons t1 t2) |  isDBValue t  
  = assert (isDBValue t) 
  ? assert (isDBValue t1) ? assert (isDBValue t2)
  ? safeDBValue t1    ? safeDBValue t2
  ? assert (ςTerm t1) ? assert (ςTerm t2)
  ? assert (ςTerm t)
safeDBValue t@THole 
  = assert (isDBValue t) &&& assert (ςTerm t)
safeDBValue t 
  = assert (not (isDBValue t))

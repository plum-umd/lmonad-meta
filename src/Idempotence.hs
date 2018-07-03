{-@ LIQUID "--reflection"  @-}

module Idempotence where

import DBValueErase
import ProofCombinators 
import Programs
import Labels 
import Prelude hiding (Maybe(..), fromJust, isJust)


{-@ εTermIdempotent :: (Eq l, Label l) => l:l -> t:Term l -> { εTerm l (εTerm l t) = εTerm l t } @-} 
εTermIdempotent   :: (Eq l, Label l) => l -> Term l -> Proof 
εTermIdempotent l t@TException 
  =   εTerm l (εTerm l t) 
  ==. εTerm l t 
  *** QED 
εTermIdempotent l t@THole 
  =   εTerm l (εTerm l t) 
  ==. εTerm l t 
  *** QED
εTermIdempotent l t@TUnit 
  =   εTerm l (εTerm l t) 
  ==. εTerm l t 
  *** QED
εTermIdempotent l t@(TInt _) 
  =   εTerm l (εTerm l t) 
  ==. εTerm l t 
  *** QED
εTermIdempotent l t@(TPred _) 
  =   εTerm l (εTerm l t) 
  ==. εTerm l t 
  *** QED
εTermIdempotent l t@TNil 
  =   εTerm l (εTerm l t) 
  ==. εTerm l t 
  *** QED
εTermIdempotent l (TCons h t) 
  =   εTerm l (εTerm l (TCons h t)) 
  ==. εTerm l (TCons (εTerm l h) (εTerm l t)) 
  ==. TCons (εTerm l (εTerm l h)) (εTerm l (εTerm l t))
       ?εTermIdempotent l h &&& εTermIdempotent l t 
  ==. TCons (εTerm l h) (εTerm l t)
  ==. εTerm l (TCons h t) 
  *** QED
εTermIdempotent l (TLabeled l1 t) 
  | l1 `canFlowTo` l 
  =   εTerm l (εTerm l (TLabeled l1 t)) 
  ==. εTerm l (TLabeled l1 (εTerm l t)) 
  ==. TLabeled l1 (εTerm l (εTerm l t)) 
      ? εTermIdempotent l t 
  ==. TLabeled l1 (εTerm l t) 
  ==. εTerm l (TLabeled l1 t) 
  *** QED

εTermIdempotent l (TLabeled l1 t) 
  =   εTerm l (εTerm l (TLabeled l1 t)) 
  ==. εTerm l (TLabeled l1 THole) 
  ==. TLabeled l1 THole
  ==. εTerm l (TLabeled l1 t) 
  *** QED

εTermIdempotent l (TInsert n t1 t2) 
  =   εTerm l (εTerm l (TInsert n t1 t2)) 
  ==. εTerm l (TInsert n (εTerm l t1) (εTerm l t2)) 
  ==. TInsert n (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2)) 
       ? εTermIdempotent l t1 &&& εTermIdempotent l t2
  ==. TInsert n (εTerm l t1) (εTerm l t2) 
  ==. εTerm l (TInsert n t1 t2) 
  *** QED 
εTermIdempotent l (TSelect n t) 
  =   εTerm l (εTerm l (TSelect n t)) 
  ==. εTerm l (TSelect n (εTerm l t)) 
  ==. TSelect n (εTerm l (εTerm l t)) 
       ? εTermIdempotent l t 
  ==. TSelect n (εTerm l t) 
  ==. εTerm l (TSelect n t) 
  *** QED 
εTermIdempotent l (TDelete n t) 
  =   εTerm l (εTerm l (TDelete n t)) 
  ==. εTerm l (TDelete n (εTerm l t)) 
  ==. TDelete n (εTerm l (εTerm l t)) 
       ? εTermIdempotent l t 
  ==. TDelete n (εTerm l t) 
  ==. εTerm l (TDelete n t) 
  *** QED 
εTermIdempotent l (TUpdate n t1 t2 t3) 
  =   εTerm l (εTerm l (TUpdate n t1 t2 t3)) 
  ==. εTerm l (TUpdate n (εTerm l t1) (εTerm l t2) (εTerm l t3)) 
  ==. TUpdate n (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2)) (εTerm l (εTerm l t3)) 
       ? εTermIdempotent l t1 &&& εTermIdempotent l t2 &&& εTermIdempotent l t3 
  ==. TUpdate n (εTerm l t1) (εTerm l t2) (εTerm l t3) 
  ==. εTerm l (TUpdate n t1 t2 t2) 
  *** QED 

εTermIdempotent l TTrue 
  =   εTerm l (εTerm l TTrue) 
  ==. εTerm l TTrue
  *** QED

εTermIdempotent l TFalse 
  =   εTerm l (εTerm l TFalse) 
  ==. εTerm l TFalse
  *** QED

εTermIdempotent l (TIf t1 t2 t3) 
  =   εTerm l (εTerm l (TIf t1 t2 t3)) 
  ==. εTerm l (TIf (εTerm l t1) (εTerm l t2) (εTerm l t3)) 
  ==. TIf (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2)) (εTerm l (εTerm l t3)) 
      ? εTermIdempotent l t1
      ? εTermIdempotent l t2
      ? εTermIdempotent l t3
  ==. TIf (εTerm l t1) (εTerm l t2) (εTerm l t3) 
  ==. εTerm l (TIf t1 t2 t3)
  *** QED

εTermIdempotent l (TUnlabel t) 
  =   εTerm l (εTerm l (TUnlabel t)) 
  ==. εTerm l (TUnlabel (εTerm l t)) 
  ==. TUnlabel (εTerm l (εTerm l t))
      ? εTermIdempotent l t
  ==. TUnlabel (εTerm l t) 
  ==. εTerm l (TUnlabel t)
  *** QED

εTermIdempotent l (TBind t1 t2) 
  =   εTerm l (εTerm l (TBind t1 t2)) 
  ==. εTerm l (TBind (εTerm l t1) (εTerm l t2)) 
  ==. TBind (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2))
      ? εTermIdempotent l t1
      ? εTermIdempotent l t2
  ==. TBind (εTerm l t1) (εTerm l t2) 
  ==. εTerm l (TBind t1 t2)
  *** QED

εTermIdempotent l (TToLabeled t1 t2) 
  =   εTerm l (εTerm l (TToLabeled t1 t2)) 
  ==. εTerm l (TToLabeled (εTerm l t1) (εTerm l t2)) 
  ==. TToLabeled (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2))
      ? εTermIdempotent l t1
      ? εTermIdempotent l t2
  ==. TToLabeled (εTerm l t1) (εTerm l t2) 
  ==. εTerm l (TToLabeled t1 t2)
  *** QED

εTermIdempotent l (TReturn t) 
  =   εTerm l (εTerm l (TReturn t)) 
  ==. εTerm l (TReturn (εTerm l t)) 
  ==. TReturn (εTerm l (εTerm l t))
      ? εTermIdempotent l t
  ==. TReturn (εTerm l t) 
  ==. εTerm l (TReturn t)
  *** QED  

εTermIdempotent l (TLIO t) 
  =   εTerm l (εTerm l (TLIO t)) 
  ==. εTerm l (TLIO (εTerm l t)) 
  ==. TLIO (εTerm l (εTerm l t))
      ? εTermIdempotent l t
  ==. TLIO (εTerm l t) 
  ==. εTerm l (TLIO t)
  *** QED  

εTermIdempotent l (TApp t1 t2) 
  =   εTerm l (εTerm l (TApp t1 t2)) 
  ==. εTerm l (TApp (εTerm l t1) (εTerm l t2)) 
  ==. TApp (εTerm l (εTerm l t1)) (εTerm l (εTerm l t2))
      ? εTermIdempotent l t1
      ? εTermIdempotent l t2
  ==. TApp (εTerm l t1) (εTerm l t2) 
  ==. εTerm l (TApp t1 t2)
  *** QED

εTermIdempotent l (TLam x t) 
  =   εTerm l (εTerm l (TLam x t)) 
  ==. εTerm l (TLam x (εTerm l t)) 
  ==. TLam x (εTerm l (εTerm l t))
      ? εTermIdempotent l t
  ==. TLam x (εTerm l t) 
  ==. εTerm l (TLam x t)
  *** QED

εTermIdempotent l (TVar x) 
  =   εTerm l (εTerm l (TVar x)) 
  ==. εTerm l (TVar x)
  *** QED

εTermIdempotent l (TVLabel x) 
  =   εTerm l (εTerm l (TVLabel x)) 
  ==. εTerm l (TVLabel x)
  *** QED
  
{-@ εDBIdempotent
 :: (Eq l, Label l)
 => l:l
 -> t:DB l
 -> { εDB l (εDB l t) = εDB l t}
 @-}
εDBIdempotent   :: (Eq l, Label l) => l -> DB l -> Proof 
εDBIdempotent l [] 
  =   εDB l (εDB l []) 
  ==. εDB l []
  *** QED 
εDBIdempotent l (Pair n t:ts) 
  =   εDB l (εDB l (Pair n t:ts)) 
  ==. εDB l (Pair n (εTable l t):(εDB l ts))
  ==. Pair n (εTable l (εTable l t)):(εDB l (εDB l ts))
      ? εTableIdempotent l t &&& εDBIdempotent l ts 
  ==. Pair n (εTable l t):(εDB l ts)
  ==. εDB l (Pair n t:ts)
  *** QED 

{-@ εTableIdempotent 
 :: Label l 
 => l:l 
 -> t:Table l
 -> { εTable l (εTable l t) = εTable l t }
 @-}
εTableIdempotent   :: (Eq l, Label l) => l -> Table l -> Proof 
εTableIdempotent l (Table ti r) 
  | not (tableLabel ti `canFlowTo` l)
  =   εTable l (εTable l (Table ti r)) 
  ==. εTable l (Table ti []) 
  ==. Table ti [] 
  ==. εTable l (Table ti r) 
  *** QED 
εTableIdempotent l (Table ti r) 
  =   εTable l (εTable l (Table ti r)) 
  ==. εTable l (Table ti (εRows l ti r)) 
  ==. Table ti (εRows l ti (εRows l ti r))
       ? εRowsIdempotent l ti r  
  ==. Table ti (εRows l ti r) 
  ==. εTable l (Table ti r) 
  *** QED 

{-@ εRowIdempotent 
 :: Label l 
 => l:l 
 -> ti:TInfo l
 -> r:Row l 
  -> { εRow l ti (εRow l ti r) = εRow l ti r }  @-}
εRowIdempotent   :: (Eq l, Label l) => l -> TInfo l -> Row l -> Proof 
εRowIdempotent l ti r@(Row k v1 v2) 
    | not (field1Label ti `canFlowTo` l) 
    =   εRow l ti (εRow l ti r)
    ==. εRow l ti (Row k THole THole)
    ==. Row k THole THole
    ==. εRow l ti r
    *** QED

εRowIdempotent l ti r@(Row k v1 v2)
    | makeValLabel ti v1 `canFlowTo` l
    =   εRow l ti (εRow l ti r)
    ==. εRow l ti (Row k (εTerm l v1) (εTerm l v2))
    ==. εRow l ti (Row k v1 (εTerm l v2))
    ==. Row k (εTerm l v1) (εTerm l (εTerm l v2))
        ? εTermIdempotent l v2
    ==. Row k (εTerm l v1) (εTerm l v2)
    ==. εRow l ti r
    *** QED

εRowIdempotent l ti r@(Row k v1 v2)
    =   εRow l ti (εRow l ti r)
    ==. εRow l ti (Row k (εTerm l v1) (εTerm l THole))
    ==. εRow l ti (Row k v1 (εTerm l THole))
    ==. εRow l ti (Row k v1 THole)
    ==. Row k (εTerm l v1) (εTerm l THole)
    ==. εRow l ti r
    *** QED

{-@ εRowsIdempotent 
 :: Label l 
 => l:l 
 -> ti:TInfo l
 -> rs:[Row l] 
  -> { εRows l ti (εRows l ti rs) = εRows l ti rs }  @-}
εRowsIdempotent   :: (Eq l, Label l) => l -> TInfo l -> [Row l] -> Proof 
εRowsIdempotent l ti []
  =   εRows l ti (εRows l ti []) 
  ==. εRows l ti []
  *** QED 

εRowsIdempotent l ti (r:rs)
    =   εRows l ti (εRows l ti (r:rs))
    ==. εRows l ti (εRow l ti r:εRows l ti rs)
    ==. εRow l ti (εRow l ti r):εRows l ti (εRows l ti rs)
        ? εRowIdempotent l ti r
    ==. εRow l ti r:εRows l ti (εRows l ti rs)
        ? εRowsIdempotent l ti rs
    ==. εRow l ti r:εRows l ti rs
    ==. εRows l ti (r:rs)
    *** QED

-- 
-- 
-- -- εRowsIdempotent l ti ((Row k v1 v2):rs)
-- --     =   εRows l ti (εRows l ti ((Row k v1 v2):rs))
-- --     ==. εRows l ti ((εRow l ti (Row k v1 v2)):(εRows l ti rs))
-- --     ==. εRows l ti (Row k v1' v2':(εRows l ti rs))
-- --     ==. εRows l ti ((Row k v1 v2):rs)
-- --     *** QED
-- εRowsIdempotent l ti ((Row k v1 v2):rs)
--   | field1Label ti `canFlowTo` l
--   =   εRows l ti (εRows l ti ((Row k v1 v2):rs)) 
--   ==. εRows l ti ((εRow l ti (Row k v1 v2)):(εRows l ti rs))
--   ==. εRows l ti (Row k v1 v2':εRows l ti rs)
--   ==. εRow l ti (Row k v1 v2'):εRows l ti (εRows l ti rs) 
--   ==. Row k v1 v2':εRows l ti (εRows l ti rs) 
--   ==. Row k v1 v2':εRows l ti (εRows l ti rs) 
--        ? εRowsIdempotent l ti rs 
--   ==. Row k v1 v2':εRows l ti rs 
--   ==. εRow l ti (Row k v1 v2):εRows l ti rs 
--   ==. εRows l ti ((Row k v1 v2):rs)
--   *** QED 
--     where
--           v2' = if makeValLabel ti v1 `canFlowTo` l then v2 else THole
-- 
-- εRowsIdempotent l ti ((Row k v1 v2):rs)
--   | not (field1Label ti `canFlowTo` l)
--   =    εRows l ti (εRows l ti ((Row k v1 v2):rs))
--   ==. εRows l ti ((εRow l ti (Row k v1 v2)):(εRows l ti rs))
--   ==. εRows l ti (Row k THole THole:εRows l ti rs)
--   ==. εRow l ti (Row k THole THole):εRows l ti (εRows l ti rs)
--   ==. Row k THole THole:εRows l ti (εRows l ti rs)
--   ==. Row k THole THole:εRows l ti rs
--        ? εRowsIdempotent l ti rs 
--   ==. Row k THole THole:εRows l ti rs 
--   ==. εRow l ti (Row k v1 v2):εRows l ti rs 
--   ==. εRows l ti ((Row k v1 v2):rs)
--   *** QED 
-- 

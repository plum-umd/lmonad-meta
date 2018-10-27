{-@ LIQUID "--reflection"  @-}

module Simulations.TUpdateFound where

import ProofCombinators
import Labels 
import Programs 

import Idempotence 
import EraseTableAny 
import LookupTableErase 
import LabelPredEraseEqual
import LabelUpdateCheck
import Simulations.Terms 
import Simulations.Update 
import Simulations.UpdateOne

import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ simulationsUpdateFlowsFound  
  :: Label l => l:l 
  -> lc:{l | canFlowTo lc l }
  -> db:DB l 
  -> n:TName 
  -> p:Pred l
  -> l1:l
  -> v1:{t:Term l | isDBValue t && ςTerm t } 
  -> l2:l
  -> v2:{t:Term l | isDBValue t && ςTerm t }
  -> t:{Table l  | Just t == lookupTable n db } 
  -> εt:{Table l | (Just εt == lookupTable n (εDB l db)) && (tableInfo t == tableInfo εt) } 
  -> { ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2))))) == ε l (eval (Pg lc db (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2)))) } 
  @-}
simulationsUpdateFlowsFound :: (Label l, Eq l) 
  => l -> l -> DB l -> TName -> Pred l -> l -> Term l -> l -> Term l -> Table l -> Table l -> Proof

simulationsUpdateFlowsFound l lc db n p l1 v1 l2 v2 t εt
  | a && εa  
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) (εTerm l (TLabeled l1 v1)) (εTerm l (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p) (TLabeled l1 εv1) (TLabeled l2 εv2)))) 
  ==. ε l (Pg εlc' (updateDB (εDB l db) n p εv1 εv2) (TReturn TUnit))
  ==. (if εlc' `canFlowTo` l 
         then Pg εlc' (εDB l (updateDB (εDB l db) n p εv1 εv2)) (εTerm l (TReturn TUnit))
         else PgHole  (εDB l (updateDB (εDB l db) n p εv1 εv2))
      )
      ? globals 
  ==. (if field1Label ti `join` l1 `canFlowTo` l 
         then Pg εlc' (εDB l (updateDB (εDB l db) n p εv1 εv2)) (εTerm l (TReturn TUnit))
              ? assert (εlc' == lc')
         else PgHole  (εDB l (updateDB (εDB l db) n p εv1 εv2))
      )
      ? globals 
      ? assert (updateLabelCheck lc t p l1 v1 l2 v2)
      ? simulationsUpdate l lc db n p l1 v1 l2 v2 t εt 
      ? assert (εDB l (updateDB (εDB l db) n p εv1 εv2) == εDB l (updateDB db n p v1 v2)) 
  ==. (if (field1Label ti `join` l1) `canFlowTo` l  
        then Pg lc' (εDB l (updateDB db n p v1 v2)) (εTerm l (TReturn TUnit))
        else PgHole (εDB l (updateDB db n p v1 v2)))
      ? globals
  ==. (if lc' `canFlowTo` l  
        then Pg lc' (εDB l (updateDB db n p v1 v2)) (εTerm l (TReturn TUnit))
        else PgHole (εDB l (updateDB db n p v1 v2)))
  ==. ε l (Pg lc' (updateDB db n p v1 v2) (TReturn TUnit))
  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2))))
  *** QED
  | not (canFlowTo (tableLabel ti) l)
  -- TUpdateFound.C2: 
  {- The erased always succeds 
     The non erased can succed or fail depending on whether the table is empty or not
  -}
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) (εTerm l (TLabeled l1 v1)) (εTerm l (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p) (TLabeled l1 εv1) (TLabeled l2 εv2)))) 
  ==. ε l (if εa 
            then Pg εlc' (updateDB (εDB l db) n p εv1 εv2) (TReturn TUnit)
            else Pg εlc' (εDB l db) (TReturn TException))
      ? globals
      ? assert (not (εlc' `canFlowTo` l))
  ==. (if εa 
         then PgHole (εDB l (updateDB (εDB l db) n p εv1 εv2)) 
         else PgHole (εDB l (εDB l db)))
      ? εTableAny l n (εDB l db) p εv1 εv2
  ==. PgHole (εDB l (εDB l db))
       ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
      ? εTableAny l n db p v1 v2
  ==.(if a  
        then PgHole (εDB l (updateDB db n p v1 v2))
        else PgHole (εDB l db))
      ? globals
      ? assert (not (εlc' `canFlowTo` l))
  ==. ε l (if a 
            then Pg lc' (updateDB db n p v1 v2) (TReturn TUnit)
            else Pg lc' db (TReturn TException)) 
  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2))))
  *** QED 


  | a && not εa  
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) (εTerm l (TLabeled l1 v1)) (εTerm l (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p) (TLabeled l1 εv1) (TLabeled l2 εv2)))) 
  ==. ε l (Pg εlc' (εDB l db) (TReturn TException)) 
  ==. (if εlc' `canFlowTo` l 
         then Pg εlc' (εDB l (εDB l db)) (εTerm l (TReturn TException))
         else PgHole  (εDB l (εDB l db))
      )
      ? globals  
  ==. (if (field1Label ti `join` l1) `canFlowTo` l  
        then Pg εlc' (εDB l (εDB l db)) (εTerm l (TReturn TException))
             ? globals
             ? assert (εTable l t == fromJust (lookupTable n (εDB l db)))
             ? labelUpdateCheckEq l lc p l1 v1 l2 v2 t
              -- TUpdateFound.C1: raising with l1 and field 1 ensures that εlc' == lc' 
        else PgHole (εDB l (εDB l db)))
      ? globals
  ==. PgHole (εDB l (εDB l db))
      ? εDBIdempotent l db 
  ==. PgHole (εDB l db)
      ? simulationsUpdateOne l lc db n p l1 v1 l2 v2 t εt  
  ==. PgHole (εDB l (updateDB db n p v1 v2))
      ? globals  
  ==. (if (field1Label ti `join` l1) `canFlowTo` l  
        then Pg lc' (εDB l (updateDB db n p v1 v2)) (εTerm l (TReturn TUnit))
        else PgHole (εDB l (updateDB db n p v1 v2)))
      ? globals
  ==. (if lc' `canFlowTo` l  
        then Pg lc' (εDB l (updateDB db n p v1 v2)) (εTerm l (TReturn TUnit))
        else PgHole (εDB l (updateDB db n p v1 v2)))
  ==. ε l (Pg lc' (updateDB db n p v1 v2) (TReturn TUnit))
  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2))))
  *** QED 
  | not a && εa 
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) (εTerm l (TLabeled l1 v1)) (εTerm l (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p) (TLabeled l1 εv1) (TLabeled l2 εv2)))) 
  ==. ε l (Pg εlc' (updateDB (εDB l db) n p εv1 εv2) (TReturn TUnit))
  ==. (if εlc' `canFlowTo` l 
         then Pg εlc' (εDB l (updateDB (εDB l db) n p εv1 εv2)) (εTerm l (TReturn TUnit))
         else PgHole  (εDB l (updateDB (εDB l db) n p εv1 εv2))
      )
      ? globals 
  ==. (if (field1Label ti `join` l1) `canFlowTo` l 
         then Pg εlc' (εDB l (updateDB (εDB l db) n p εv1 εv2)) (εTerm l (TReturn TUnit))
              ? labelUpdateCheckEq l lc p l1 v1 l2 v2 t
              -- TUpdateFound.C1: raising with l1 and field 1 ensures that εlc' == lc' 
         else PgHole  (εDB l (updateDB (εDB l db) n p εv1 εv2))
      )
      ? globals 
  ==. PgHole  (εDB l (updateDB (εDB l db) n p εv1 εv2))
      ? simulationsUpdateOneErased l lc db n p l1 v1 l2 v2 t εt
  ==. PgHole (εDB l db) 
      ? globals 
      ? labelUpdateCheckEq l lc p l1 v1 l2 v2 t
      ? assert (not ((join (field1Label ti) l1) `canFlowTo` l))
      ? assert (not (lc' `canFlowTo` l))
  ==. ε l (Pg lc' db (TReturn TException))
  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2))))
  *** QED 
  | not a && not εa 
  =   ε l (eval (ε l (Pg lc db (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (εTerm l (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (εTerm l (TPred p)) (εTerm l (TLabeled l1 v1)) (εTerm l (TLabeled l2 v2))))) 
  ==. ε l (eval (Pg lc (εDB l db) (TUpdate n (TPred p) (TLabeled l1 εv1) (TLabeled l2 εv2)))) 
  ==. ε l (Pg εlc' (εDB l db) (TReturn TException)) 
      ? assert (lc' == εlc') 
  ==. ε l (Pg lc' (εDB l db) (TReturn TException)) 
  ==. (if lc' `canFlowTo` l 
        then Pg lc' (εDB l (εDB l db)) (εTerm l (TReturn TException))
        else PgHole (εDB l (εDB l db)))
      ? εDBIdempotent l db 
  ==. (if lc' `canFlowTo` l 
        then Pg lc' (εDB l db) (εTerm l (TReturn TException))
        else PgHole (εDB l db))
  ==. ε l (Pg lc' db (TReturn TException))
  ==. ε l (eval (Pg lc db (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2))))
  *** QED 
  where
    ti = tableInfo t

    a  = updateLabelCheck lc t  p l1 v1  l2 v2
    εa = updateLabelCheck lc εt p l1 εv1 l2 εv2

    lc'  = lc `join` ((field1Label ti `join` l1) `join` tableLabel (tableInfo t))
    εlc' = lc `join` ((field1Label ti `join` l1) `join` tableLabel (tableInfo t))

    εv1  = if l1 `canFlowTo` l then (εTerm l v1) else THole
    εv2  = if l2 `canFlowTo` l then (εTerm l v2) else THole

    globals = assert (Just t  == lookupTable n db) 
              ? assert (Just εt == lookupTable n (εDB l db)) 
              ? pTable n l db t 
              ? assert (Just (εTable l t) == lookupTable n (εDB l db))
              ? joinCanFlowTo lc ((field1Label ti `join` l1) `join` tableLabel (tableInfo t)) l
              ? joinCanFlowTo (field1Label ti `join` l1) (tableLabel (tableInfo t)) l
              ? joinCanFlowTo (field1Label ti) l1 l


{-@ getInv :: ti:TInfo l -> {canFlowTo (field1Label ti) (tableLabel ti)} @-} 
getInv :: TInfo l -> Proof 
getInv (TInfo _ _ _ _ _) = ()
      

pTable :: (Eq l, Label l) => TName -> l -> DB l -> Table l -> Proof 
{-@ pTable :: (Eq l, Label l) =>  n:TName -> l:l -> db:DB l 
    -> t:{Table l | Just t == lookupTable n db && isJust (lookupTable n db) }
    -> {Just (εTable l t) == lookupTable n (εDB l db)} / [len db] @-}
pTable n l [] t = Nothing ==. lookupTable n [] *** QED 
pTable n l db'@(Pair n' t':ts) t | n == n' 
      =   lookupTable n (εDB l (Pair n' t':ts))
      ==. lookupTable n (Pair n' (εTable l t'):εDB l ts)
      ==. Just (εTable l t') 
      ==. Just (εTable l (fromJust (Just t')))
      ==. Just (εTable l (fromJust (lookupTable n (Pair n' t':ts))))
      *** QED 
      
pTable n l db'@(Pair n' t':ts) t 
      =   Just (εTable l (fromJust (lookupTable n (Pair n' t':ts))))
      ==. Just (εTable l (fromJust (lookupTable n ts)))
      ==. lookupTable n (εDB l ts) ? pTable n l ts t 
      ==. lookupTable n (Pair n' (εTable l t'):εDB l ts)
      ==. lookupTable n (εDB l (Pair n' t':ts))
      *** QED 



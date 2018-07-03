{-@ LIQUID "--reflection"  @-}

module Simulations.Insert where

import ProofCombinators
import Labels 
import Programs 

import Idempotence 
import Simulations.Terms 
import TableInfoErase

import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ insertDBRowErase :: (Eq l, Label l) => l:l -> n:TName -> db:DB l -> t : {TInfo l | Just t == lookupTableInfo n db} -> r:Row l -> {εDB l (insertDB db n r) == εDB l (insertDB db n (εRow l t r)) } @-}
insertDBRowErase :: (Eq l, Label l) => l -> TName -> DB l -> TInfo l -> Row l -> Proof
insertDBRowErase l n db@[] ti r =
        εDB l (insertDB db n r)
    ==. εDB l (insertDB db n (εRow l ti r))
    *** QED

insertDBRowErase l n db@(Pair n' t@(Table tinfo rs):ts) ti r
    | n == n'
    , not (tableLabel tinfo `canFlowTo` l)
    =   εDB l (insertDB db n r)
    ==. εDB l (insertDB (Pair n t:ts) n r)
    ==. εDB l (Pair n (insertTable t r):ts)
    ==. εDB l (Pair n (Table tinfo (r:rs)):ts)
    ==. (Pair n (εTable l (Table tinfo (r:rs)))):(εDB l ts)
    ==. (Pair n (Table tinfo [])):(εDB l ts)

    ==. (Pair n (εTable l (Table tinfo ((εRow l ti r):rs)))):(εDB l ts)
    ==. εDB l (Pair n (Table tinfo ((εRow l ti r):rs)):ts)
    ==. εDB l (Pair n (insertTable t (εRow l ti r)):ts)
    ==. εDB l (insertDB (Pair n t:ts) n (εRow l ti r))
    ==. εDB l (insertDB db n (εRow l ti r))
    *** QED

insertDBRowErase l n db@(Pair n' t@(Table tinfo rs):ts) ti r
    | n == n'
    =   εDB l (insertDB db n r)
    ==. εDB l (insertDB (Pair n t:ts) n r)
    ==. εDB l (Pair n (insertTable t r):ts)
    ==. εDB l (Pair n (Table tinfo (r:rs)):ts)
    ==. (Pair n (εTable l (Table tinfo (r:rs)))):(εDB l ts)
    ==. (Pair n (Table tinfo (εRows l tinfo (r:rs)))):(εDB l ts)
    ==. (Pair n (Table tinfo (εRow l tinfo r:εRows l tinfo rs))):(εDB l ts)

        ? εRowIdempotent l tinfo r

    ==. (Pair n (Table tinfo ((εRow l tinfo (εRow l tinfo r)):εRows l tinfo rs))):(εDB l ts)
        ? tinfoEqual n n' db ti rs tinfo
    ==. (Pair n (Table tinfo ((εRow l tinfo (εRow l ti r)):εRows l tinfo rs))):(εDB l ts)
    ==. (Pair n (Table tinfo (εRows l tinfo (εRow l ti r:rs)))):(εDB l ts)
    ==. (Pair n (εTable l (Table tinfo ((εRow l ti r):rs)))):(εDB l ts)
    ==. εDB l (Pair n (Table tinfo ((εRow l ti r):rs)):ts)
    ==. εDB l (Pair n (insertTable t (εRow l ti r)):ts)
    ==. εDB l (insertDB (Pair n t:ts) n (εRow l ti r))
    ==. εDB l (insertDB db n (εRow l ti r))
    *** QED

insertDBRowErase l n db@(Pair n' t@(Table tinfo rs):ts) ti r
    =   εDB l (insertDB db n r)
    ==. εDB l (insertDB (Pair n' t:ts) n r)
    ==. εDB l (Pair n' t:(insertDB ts n r))
    ==. Pair n' (εTable l t):εDB l (insertDB ts n r)

        ?   tailTInfoEqual n n' t db
        &&& insertDBRowErase l n ts ti r

    ==. Pair n' (εTable l t):εDB l (insertDB ts n (εRow l ti r))
    ==. εDB l (Pair n' t:(insertDB ts n (εRow l ti r)))
    ==. εDB l (insertDB (Pair n' t:ts) n (εRow l ti r))
    ==. εDB l (insertDB db n (εRow l ti r))
    *** QED

{-@ inserDBTableErase :: (Eq l, Label l) => l:l -> n:TName -> db:DB l -> r:Row l -> 
   {εDB l (insertDB db n r) == εDB l (insertDB (εDB l db) n r) } @-}
inserDBTableErase :: (Eq l, Label l) => l -> TName -> DB l -> Row l -> Proof 
inserDBTableErase l n [] r
  =   εDB l (insertDB [] n r) 
  ==. εDB l (insertDB (εDB l []) n r) 
  *** QED 

inserDBTableErase l n (Pair n' (Table tinfo rs):ts) r
  | n == n', not (tableLabel tinfo `canFlowTo` l) 
  =   εDB l (insertDB (Pair n' (Table tinfo rs):ts) n r) 
  ==. εDB l (Pair n' (insertTable (Table tinfo rs) r):ts)
  ==. εDB l (Pair n' (Table tinfo (r:rs)):ts)
  ==. Pair n' (εTable l (Table tinfo (r:rs))):(εDB l ts)
  ==. Pair n' (Table tinfo []):(εDB l ts)
       ? εDBIdempotent l ts 
  ==. Pair n' (Table tinfo []):(εDB l (εDB l ts)) 
  ==. Pair n' (εTable l (Table tinfo [r])):(εDB l (εDB l ts)) 
  ==. εDB l (Pair n' (Table tinfo [r]):(εDB l ts)) 
  ==. εDB l (Pair n' (insertTable (Table tinfo []) r):(εDB l ts)) 
  ==. εDB l (Pair n' (insertTable (εTable l (Table tinfo rs)) r):(εDB l ts)) 
  ==. εDB l (insertDB (Pair n' (εTable l (Table tinfo rs)):(εDB l ts)) n r) 
  ==. εDB l (insertDB (εDB l (Pair n' (Table tinfo rs):ts)) n r) 
  *** QED 


inserDBTableErase l n (Pair n' (Table tinfo rs):ts) r
  | n == n' 
  =   εDB l (insertDB (Pair n' (Table tinfo rs):ts) n r) 
  ==. εDB l (Pair n' (insertTable (Table tinfo rs) r):ts)
  ==. εDB l (Pair n' (Table tinfo (r:rs)):ts)
  ==. Pair n' (εTable l (Table tinfo (r:rs))):(εDB l ts)
  ==. Pair n' (Table tinfo (εRows l tinfo (r:rs))):(εDB l ts)
  ==. Pair n' (Table tinfo (εRow l tinfo r:εRows l tinfo rs)):(εDB l ts)
       ? εRowsIdempotent l tinfo rs &&& εDBIdempotent l ts 
  ==. Pair n' (Table tinfo (εRow l tinfo r:εRows l tinfo (εRows l tinfo rs))):(εDB l (εDB l ts)) 
  ==. Pair n' (Table tinfo (εRows l tinfo (r:εRows l tinfo rs))):(εDB l (εDB l ts)) 
  ==. Pair n' (εTable l (Table tinfo (r:εRows l tinfo rs))):(εDB l (εDB l ts)) 
  ==. εDB l (Pair n' (Table tinfo (r:εRows l tinfo rs)):(εDB l ts)) 
  ==. εDB l (Pair n' (insertTable (Table tinfo (εRows l tinfo rs)) r):(εDB l ts)) 
  ==. εDB l (Pair n' (insertTable (εTable l (Table tinfo rs)) r):(εDB l ts)) 
  ==. εDB l (insertDB (Pair n' (εTable l (Table tinfo rs)):(εDB l ts)) n r) 
  ==. εDB l (insertDB (εDB l (Pair n' (Table tinfo rs):ts)) n r) 
  *** QED 


inserDBTableErase l n (Pair n' t:ts) r
  =   εDB l (insertDB (Pair n' t:ts) n r) 
  ==. εDB l (Pair n' t:insertDB ts n r) 
  ==. Pair n' (εTable l t):εDB l (insertDB ts n r) 
      ? inserDBTableErase l n ts r  
  ==. Pair n' (εTable l t):εDB l (insertDB (εDB l ts) n r)
      ? εTableIdempotent l t 
  ==. Pair n' (εTable l (εTable l t)): εDB l (insertDB (εDB l ts) n r) 
  ==. εDB l (Pair n' (εTable l t): insertDB (εDB l ts) n r) 
  ==. εDB l (insertDB (Pair n' (εTable l t):(εDB l ts)) n r) 
  ==. εDB l (insertDB (εDB l (Pair n' t:ts)) n r) 
  *** QED 

{-@ eraseDB :: (Eq l, Label l) => l:l -> l':l -> db:DB l -> t:Term l -> 
   {ε l (Pg l' (εDB l db) t) == ε l (Pg l' db t) } @-}
eraseDB :: (Eq l, Label l) => l -> l -> DB l -> Term l -> Proof 
eraseDB l l' db t | l' `canFlowTo` l =
        ε l (Pg l' (εDB l db) t)
    ==. Pg l' (εDB l (εDB l db)) (εTerm l t)

        ? εDBIdempotent l db

    ==. Pg l' (εDB l db) (εTerm l t)
    ==. ε l (Pg l' db t)
    *** QED
eraseDB l l' db t = 
        ε l (Pg l' (εDB l db) t)
    ==. PgHole (εDB l (εDB l db))
        
        ? εDBIdempotent l db

    ==. PgHole (εDB l db)
    ==. ε l (Pg l' db t)
    *** QED


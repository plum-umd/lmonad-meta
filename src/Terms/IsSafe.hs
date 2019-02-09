{-@ measure ς @-}
ς :: Program l -> Bool 
ς (PgHole _) = True 
ς (Pg _ _ t) = ςTerm t


{-@ type STerm l = {t:Term l | ςTerm t } @-}

{-@ measure ςTerm @-}
ςTerm :: Term l -> Bool 
ςTerm (TInsert _ (TLabeled _ v1) (TLabeled _ v2)) 
  =  isDBValue v1 && isDBValue v2 
  && ςTerm v1 && ςTerm v2
ςTerm (TUpdate _ (TPred _) (TJust (TLabeled _ v1)) (TJust (TLabeled _ v2))) 
  =  isDBValue v1 && isDBValue v2 
  && ςTerm v1 && ςTerm v2
ςTerm (TUpdate _ (TPred _) TNothing (TJust (TLabeled _ v2)))
  =  isDBValue v2
  && ςTerm v2
-- This is too strong as 1. it rejects insertion on expressions
-- that are evaluated to isDBValues 2. predicate expressions that 
-- are evaluated to predicates (pred expressions should satisfy erasure id)
ςTerm (TInsert _ _ _)    = False 
ςTerm (TUpdate _ _ _ _)  = False
ςTerm (TInt _)           = True 
ςTerm TUnit              = True 
ςTerm TTrue              = True 
ςTerm TFalse             = True 
ςTerm (TVLabel _)        = True
ςTerm TNil               = True 
ςTerm (TCons t1 t2)      = ςTerm t1 && ςTerm t2 
ςTerm THole              = True
ςTerm (TSelect _ t)      = ςTerm t 
ςTerm (TDelete _ t)      = ςTerm t 
ςTerm (TLabeled _ t)     = ςTerm t 
ςTerm TException         = True 
ςTerm (TPred _)          = True 
ςTerm (TIf t1 t2 t3)     = ςTerm t1 && ςTerm t2 && ςTerm t3  
ςTerm (TUnlabel t)       = ςTerm t 
ςTerm (TBind t1 t2)      = ςTerm t1 && ςTerm t2 
ςTerm (TReturn t)        = ςTerm t 
ςTerm (TLIO t)           = ςTerm t 
ςTerm (TApp t1 t2)       = ςTerm t1 && ςTerm t2 
ςTerm (TLam _ t)         = ςTerm t  
ςTerm (TVar _)           = True  
ςTerm (TToLabeled t1 t2) = ςTerm t1 && ςTerm t2
ςTerm (TJust t)          = ςTerm t
ςTerm TNothing           = True
ςTerm (TCase t1 t2 t3)   = ςTerm t1 && ςTerm t2 && ςTerm t3

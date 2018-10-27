

-- The DB values can be extended as long as they satisfy two conditions: 
-- 1. identity is erasure and 
-- 2. substitution on a isDBValue is also a isDBValue

{-@ type DBTerm l  = {t:Term l | isDBValue t } @-}
{-@	type SDBTerm l = {t:Term l | isDBValue t && ςTerm t } @-}

{-@ measure isDBValue @-}
isDBValue :: Term l -> Bool 
isDBValue (TInt _)          = True 
isDBValue TUnit             = True 
isDBValue TTrue             = True 
isDBValue TFalse            = True 
isDBValue (TVLabel _)       = True
isDBValue TNil              = True 
isDBValue (TCons t1 t2)     = isDBValue t1 && isDBValue t2 
isDBValue THole             = True
isDBValue (TInsert _ _ _)   = False 
isDBValue (TSelect _ _)     = False 
isDBValue (TDelete _ _)     = False 
isDBValue (TUpdate _ _ _ _) = False 
isDBValue (TLabeled _ _)    = False 
isDBValue TException        = False 
isDBValue (TPred _)         = False 
isDBValue (TIf _ _ _)       = False 
isDBValue (TUnlabel _)      = False 
isDBValue (TBind _ _)       = False 
isDBValue (TReturn _)       = False 
isDBValue (TLIO _)          = False 
isDBValue (TApp _ _)        = False 
isDBValue (TLam _ _)        = False  
isDBValue (TVar _)          = False  
isDBValue (TToLabeled _ _)  = False

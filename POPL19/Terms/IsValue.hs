

{-@ measure isValue @-}
isValue :: Term l -> Bool 
isValue (TInsert _ _ _)   = False 
isValue (TSelect _ _)     = False 
isValue (TDelete _ _)     = False 
isValue (TUpdate _ _ _ _) = False 
isValue (TLabeled _ _)    = True 
isValue (TInt _)          = True 
isValue TUnit             = True 
isValue THole             = True 
isValue TException        = True 
isValue (TPred _)         = True 
isValue TNil              = True 
isValue (TCons _ _)       = True 
isValue TTrue             = True 
isValue TFalse            = True 
isValue (TIf _ _ _)       = False 
isValue (TUnlabel _)      = False 
isValue (TBind _ _)       = False 
isValue (TReturn _)       = False 
isValue (TLIO _)          = True 
isValue (TApp _ _)        = False 
isValue (TLam _ _)        = True  
isValue (TVar _ )         = True  
isValue (TVLabel _)       = True
isValue (TToLabeled _ _)  = False

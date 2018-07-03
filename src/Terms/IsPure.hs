

{-@ measure isPure @-}
isPure :: Term l -> Bool 
isPure (TInsert _ _ _)   = False 
isPure (TSelect _ _)     = False 
isPure (TDelete _ _)     = False 
isPure (TUpdate _ _ _ _) = False 
isPure (TToLabeled _ _)  = False
isPure (TUnlabel _)      = False 
isPure (TBind _ _)       = False 
isPure (TReturn _)       = False 
isPure (TLIO _)          = False 
isPure (TLabeled _ _)    = True 
isPure (TInt _)          = True 
isPure TUnit             = True 
isPure THole             = True 
isPure TException        = True 
isPure (TPred _)         = True 
isPure TNil              = True 
isPure (TCons _ _)       = True 
isPure TTrue             = True 
isPure TFalse            = True 
isPure (TIf _ _ _)       = True 
isPure (TApp _ _)        = True 
isPure (TLam _ _)        = True  
isPure (TVar _ )         = True  
isPure (TVLabel _)       = True

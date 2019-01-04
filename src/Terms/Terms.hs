

type Var = String 


data Term l 
  = TInsert TName (Term l) (Term l)
  | TSelect TName (Term l)
  | TDelete TName (Term l)
  | TUpdate TName (Term l) (Term l) (Term l)
  | TLabeled l (Term l)
  | TInt Int 
  | TUnit 
  | THole 
  | TException
  | TPred Pred 
  | TNil 
  | TCons (Term l) (Term l)
  | TTrue 
  | TFalse 
  | TIf (Term l) (Term l) (Term l)
  | TUnlabel (Term l)
  | TBind (Term l) (Term l)
  | TReturn (Term l)
  | TLIO (Term l) 
  | TApp (Term l) (Term l) 
  | TLam Var (Term l) 
  | TVar Var
  | TToLabeled (Term l) (Term l)
  | TVLabel l
  -- | optional parameter
  | TJust (Term l)
  -- | optional parameter (omitted)
  | TNothing
  deriving Eq 

{-@ reflect tInt @-}
{-@ tInt :: i:Int -> {t:Term l | t == TInt i && isDBValue t} @-}
tInt :: Int -> Term l 
tInt i = TInt i 

isTInt (TInt _) = True 
isTInt _        = False 

{-@ measure isTLabeled @-}
isTLabeled :: Term l -> Bool 
isTLabeled (TLabeled _ _) = True 
isTLabeled _              = False 

{-@ measure isTPred @-}
isTPred :: Term l -> Bool 
isTPred (TPred _) = True
isTPred _         = False 

{-@ measure isTLIO @-}
isTLIO :: Term l -> Bool 
isTLIO (TLIO _) = True
isTLIO _        = False 

{-@ measure fromTLIO @-}
{-@ fromTLIO :: {t:Term l | isTLIO t} -> {o:Term l | t == TLIO o} @-} 
fromTLIO :: Term l -> Term l 
fromTLIO (TLIO t) = t



data TName = TName Int
  deriving Eq  
{-@ data Term [tsize] @-}


{-@ measure tsize @-}
tsize :: Term l -> Int
{-@ tsize :: Term l -> Nat @-}
tsize (TInsert _ t1 t2)    = 1 + tsize t1 + tsize t2
tsize (TSelect _ t)        = 1 + tsize t
tsize (TDelete _ t)        = 1 + tsize t
tsize (TUpdate _ t1 t2 t3) = 1 + tsize t1 + tsize t2 + tsize t3 
tsize (TLabeled _ t)       = 1 + tsize t 
tsize (TInt _)             = 0
tsize (TPred _)            = 0
tsize TUnit                = 0
tsize THole                = 0
tsize TNil                 = 0
tsize (TCons h t)          = 1 + tsize h + tsize t 
tsize TException           = 0
tsize TTrue                = 0
tsize TFalse               = 0
tsize (TIf t1 t2 t3)       = 1 + tsize t1 + tsize t2 + tsize t3
tsize (TUnlabel t)         = 1 + tsize t 
tsize (TBind t1 t2)        = 1 + tsize t1 + tsize t2 
tsize (TToLabeled t1 t2)   = 1 + tsize t1 + tsize t2 
tsize (TReturn t)          = 1 + tsize t 
tsize (TLIO t)             = 1 + tsize t 
tsize (TApp t1 t2)         = 1 + tsize t1 + tsize t2 
tsize (TVar _)             = 0 
tsize (TVLabel _)          = 0 
tsize (TLam _ t)           = 1 + tsize t 
tsize (TJust t)            = 1 + tsize t
tsize TNothing             = 0



{-@ reflect εTerm @-}

{-@ εTerm 
  :: Label l 
  => l 
  -> ti:Term l 
  -> {to:Term l | (isDBValue ti => to == ti) 
               && (isDBValue to =>  isDBValue ti) 
               && (isValue ti <=> isValue to) 
               && (isPure ti => isPure to) 
               && (isTLIO ti <=> isTLIO to)} @-}
εTerm :: Label l => l -> Term l -> Term l 
εTerm l (TLabeled l1 v)
  | l1 `canFlowTo` l 
  = TLabeled l1 (εTerm l v)
  | otherwise
  = TLabeled l1 THole 
εTerm _ (TInt i)
  = TInt i 
εTerm _ THole
  = THole
εTerm _ TUnit
  = TUnit
εTerm _ TNil
  = TNil
εTerm l (TCons h t) 
  = TCons (εTerm l h) (εTerm l t)
εTerm _ (TPred p)
  = TPred p 
εTerm _ TException
  = TException
εTerm l (TInsert n t1 t2) 
  = TInsert n (εTerm l t1) (εTerm l t2)
εTerm l (TSelect n t) 
  = TSelect n (εTerm l t)
εTerm l (TDelete n t) 
  = TDelete n (εTerm l t)
εTerm l (TUpdate n t1 t2 t3) 
  = TUpdate n (εTerm l t1) (εTerm l t2) (εTerm l t3)
εTerm l TTrue
  = TTrue
εTerm l TFalse
  = TFalse
εTerm l (TIf t1 t2 t3)
  = TIf (εTerm l t1) (εTerm l t2) (εTerm l t3)
εTerm l (TUnlabel t)
  = TUnlabel (εTerm l t)
εTerm l (TBind t1 t2)
  = TBind (εTerm l t1) (εTerm l t2)
εTerm l (TReturn t)
  = TReturn (εTerm l t)
εTerm l (TLIO t)
  = TLIO (εTerm l t)
εTerm l (TApp t1 t2)
  = TApp (εTerm l t1) (εTerm l t2)
εTerm l (TLam x t)
  = TLam x (εTerm l t)
εTerm l (TVar x)
  = TVar x 
εTerm l (TToLabeled t1 t2) 
  = TToLabeled (εTerm l t1) (εTerm l t2)
εTerm l t@(TVLabel _) 
  = t
εTerm l (TJust t)
  = TJust (εTerm l t)
εTerm l TNothing
  = TNothing
εTerm l (TCase t1 t2 t3)
  = TCase (εTerm l t1) (εTerm l t2) (εTerm l t3)




{-@ reflect evalTerm @-}
{-@ evalTerm :: Label l => i:Term l -> {o:Term l | ςTerm i => ςTerm o} / [tsize i] @-} 
evalTerm :: Label l => Term l -> Term l 
evalTerm (TApp (TLam x t) t2) = substProp x t2 t `cast` subst x t2 t
evalTerm (TApp t1 t2)         = TApp (evalTerm t1) t2
evalTerm (TIf TTrue  t1 t2)   = t1 
evalTerm (TIf TFalse t1 t2)   = t2
evalTerm (TIf THole t1 t2)    = THole 
evalTerm (TIf t t1 t2)        = TIf (evalTerm t) t1 t2
evalTerm t                    = t 


{-@ substProp :: x:Var -> tx:Term l -> t:Term l 
       -> { ((ςTerm tx && ςTerm t) => ςTerm (subst x tx t)) 
                   && (isDBValue t => isDBValue (subst x tx t) ) 
                   && (isTPred t => isTPred (subst x tx t) )} / [tsize t] @-} 
substProp :: Var -> Term l -> Term l -> ()
substProp x tx (TVar y)
  | x == y 
  = subst x tx (TVar y) ==. tx *** QED  
  | otherwise 
  = subst x tx (TVar y) ==. TVar y *** QED  
substProp x tx (TLam y t)
  | x == y 
  = subst x tx (TLam y t) ==. TLam y t *** QED 
  | otherwise
  = subst x tx (TLam y t) ==. TLam y (subst x tx t) 
  ? substProp x tx t *** QED 
substProp x tx (TApp t1 t2)
  = subst x tx (TApp t1 t2) ==. TApp (subst x tx t1) (subst x tx t2)
  ? substProp x tx t1
  ? substProp x tx t2
   *** QED 
substProp x tx (TLIO t)
  = subst x tx (TLIO t) ==. TLIO (subst x tx t)
  ? substProp x tx t 
  *** QED 
substProp x tx (TReturn t)
  = subst x tx (TReturn t) ==. TReturn (subst x tx t)
  ? substProp x tx t
  *** QED 

substProp x tx (TBind t1 t2)
  = subst x tx (TBind t1 t2) ==. TBind (subst x tx t1) (subst x tx t2)
  ? substProp x tx t1
  ? substProp x tx t2
   *** QED 

substProp x tx (TUnlabel t)
  = subst x tx (TUnlabel t) ==. TUnlabel (subst x tx t)
  ? substProp x tx t
  *** QED 
substProp x tx (TIf t1 t2 t3)
  = subst x tx (TIf t1 t2 t3) ==. TIf (subst x tx t1) (subst x tx t2) (subst x tx t3)
  ? substProp x tx t1
  ? substProp x tx t2
  ? substProp x tx t3
   *** QED 

substProp x tx (TCons t1 t2)
  = subst x tx (TCons t1 t2) ==. TCons (subst x tx t1) (subst x tx t2)
  ? substProp x tx t1
  ? substProp x tx t2
   *** QED 
substProp x tx (TLabeled l t)
  = subst x tx (TLabeled l t) ==. TLabeled l (subst x tx t)
  ? substProp x tx t
  *** QED   


substProp x tx (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2))
  =   subst x tx (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2)) 
  ==. TUpdate n (subst x tx (TPred p)) (subst x tx (TLabeled l1 v1)) (subst x tx (TLabeled l2 v2))
  ==. TUpdate n (TPred p) (TLabeled l1 (subst x tx v1)) (TLabeled l2 (subst x tx v2))
  ? substProp x tx v1
  ? substProp x tx v2
   *** QED 


substProp x tx (TUpdate n t1 t2 t3)
  = subst x tx (TUpdate n t1 t2 t3) ==. TUpdate n (subst x tx t1) (subst x tx t2) (subst x tx t3)
  ? substProp x tx t1
  ? substProp x tx t2
  ? substProp x tx t3
   *** QED 

substProp x tx (TInsert n (TLabeled l1 v1) (TLabeled l2 v2))
  =   subst x tx (TInsert n (TLabeled l1 v1) (TLabeled l2 v2)) 
  ==. TInsert n (subst x tx (TLabeled l1 v1)) (subst x tx (TLabeled l2 v2)) 
  ==. TInsert n (TLabeled l1 (subst x tx v1)) (TLabeled l2 (subst x tx v2)) 
  ? substProp x tx v1
  ? substProp x tx v2
   *** QED 


substProp x tx (TInsert n t1 t2)
  = subst x tx (TInsert n t1 t2) ==. TInsert n (subst x tx t1) (subst x tx t2)
  ? substProp x tx t1
  ? substProp x tx t2
   *** QED 
substProp x tx (TSelect n t)
  = subst x tx (TSelect n t) ==. TSelect n (subst x tx t)
  ? substProp x tx t
  *** QED  
substProp x tx (TDelete n t)
  = subst x tx (TDelete n t) ==. TDelete n (subst x tx t)
  ? substProp x tx t
  *** QED  
substProp x tx (TToLabeled t1 t2)  
  = subst x tx (TToLabeled t1 t2) ==. TToLabeled (subst x tx t1) (subst x tx t2)
  ? substProp x tx t1
  ? substProp x tx t2
   *** QED 
substProp x tx t 
  = subst x tx t ==. t *** QED 

{-@ reflect subst @-}
{-@ subst :: Var -> Term l -> t:Term l -> Term l /[tsize t] @-}
subst :: Var -> Term l -> Term l -> Term l 
subst x tx (TVar y)
  | x == y 
  = tx 
  | otherwise 
  = TVar y 
subst x tx (TLam y t)
  | x == y 
  = TLam y t 
  | otherwise
  = TLam y (subst x tx t)
subst x tx (TApp t1 t2)
  = TApp (subst x tx t1) (subst x tx t2)
subst x tx (TLIO t)
  = TLIO (subst x tx t)
subst x tx (TReturn t)
  = TReturn (subst x tx t)
subst x tx (TBind t1 t2)
  = TBind (subst x tx t1) (subst x tx t2)
subst x tx (TUnlabel t)
  = TUnlabel (subst x tx t)
subst x tx (TIf t1 t2 t3)
  = TIf (subst x tx t1) (subst x tx t2) (subst x tx t3)
subst x tx (TCons t1 t2)
  = TCons (subst x tx t1) (subst x tx t2)
subst x tx (TLabeled l t)
  = TLabeled l (subst x tx t)
subst x tx (TUpdate n t1 t2 t3)
  = TUpdate n (subst x tx t1) (subst x tx t2) (subst x tx t3)
subst x tx (TInsert n t1 t2)
  = TInsert n (subst x tx t1) (subst x tx t2)
subst x tx (TSelect n t)
  = TSelect n (subst x tx t)
subst x tx (TDelete n t)
  = TDelete n (subst x tx t)
subst x tx (TToLabeled t1 t2)  
  = TToLabeled (subst x tx t1) (subst x tx t2)
subst _ _ t 
  = t 

{- 
{-@ reflect substTUpdate @-}
{-@ substTUpdate :: Var -> xt:Term l 
  -> n:TName 
  -> t1:Term l
  -> t2:Term l 
  -> t3:Term l  
       -> {o:Term l | ((ςTerm xt && ςTerm (TUpdate n t1 t2 t3)) => ςTerm o) } 
       / [(1 + tsize t1 + tsize t2 + tsize t3), 0] @-} 
substTUpdate :: Var -> Term l -> TName -> Term l -> Term l -> Term l -> Term l 

substTUpdate x tx n (TPred p) (TLabeled l1 t1) (TLabeled l2 t2)
   | isDBValue t1 && isDBValue t2
  && ςTerm t1 && ςTerm t2
  = TUpdate n (TPred (substPred x tx p)) (TLabeled l1 (subst x tx t1)) (TLabeled l2 (subst x tx t2))
substTUpdate x tx n t1 t2 t3
  = assert (not (ςTerm (TUpdate n t1 t2 t3))) `cast` 
     TUpdate n (subst x tx t1) (subst x tx t2) (subst x tx t3)

{-@ reflect substTInsert @-}
{-@ substTInsert :: Var -> xt:Term l 
  -> n:TName 
  -> t1:Term l
  -> t2:Term l 
       -> {o:Term l | ((ςTerm xt && ςTerm (TInsert n t1 t2)) => ςTerm o)  } 
       / [(1 + tsize t1 + tsize t2), 0] @-} 
substTInsert :: Var -> Term l -> TName -> Term l -> Term l -> Term l 
substTInsert x tx n (TLabeled l1 t1) (TLabeled l2 t2)
   | isDBValue t1 && isDBValue t2
  && ςTerm t1 && ςTerm t2
  = TInsert n (TLabeled l1 (subst x tx t1)) (TLabeled l2 (subst x tx t2))
substTInsert x tx n t1 t2
  = assert (not (ςTerm (TInsert n t1 t2))) `cast` 
     TInsert n (subst x tx t1) (subst x tx t2)



{-@ reflect substPred @-}
{-@ substPred :: Var -> Term l -> i:Pred -> {o:Pred | o == i} @-}
substPred :: Var -> Term l -> Pred -> Pred
substPred _ _ p = p 

-}

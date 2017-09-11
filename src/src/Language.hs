type Label = Integer
type Var   = Integer
-------------------------------------------------------------------------------
-- | Terms --------------------------------------------------------------------
-------------------------------------------------------------------------------

data Term 
  = THole
  | TLam {lamVar :: Var, lamTerm :: Term}
  | TTrue 
  | TFalse 
  | TUnit 
  | TVar {tVar :: Var}
  | TApp {tApp1 :: Term, tApp2 :: Term}
  | TFix {tFix :: Term}
  | TIF  {iIfCond :: Term, tIfThen :: Term, tIfElse :: Term} 
  deriving Eq 

{-@ data Term [size]
  = THole 
  | TLam {lamVar :: Var, lamTerm :: Term}
  | TTrue 
  | TFalse 
  | TUnit 
  | TVar {tVar :: Var}
  | TApp {tApp1 :: Term, tApp2 :: Term}
  | TFix {tFix :: Term}
  | TIF  {iIfCond :: Term, tIfThen :: Term, tIfElse :: Term} 
 @-} 

size :: Term -> Integer 
{-@ measure size @-}
{-@ invariant {t:Term | 0 <= size t} @-}
{-@ size :: Term -> {v:Integer |  0 <= v }  @-}
size (TIF t1 t2 t3) = 1 + size t1 + size t2 + size t3 
size (TFix t)       = 1 + size t 
size (TApp t1 t2)   = 1 + size t1 + size t2 
size THole          = 0
size (TVar _)       = 1 
size (TLam _ e)     = 1 + size e
size TTrue          = 1 
size TFalse         = 1 
size TUnit          = 1 

isValue :: Term -> Bool 
{-@ measure isValue @-}
isValue (TLam _ _) = True 
isValue TUnit      = True 
isValue TTrue      = True 
isValue TFalse     = True 
isValue _          = False 


-------------------------------------------------------------------------------
-- | Types --------------------------------------------------------------------
-------------------------------------------------------------------------------

data Type = TTUnit | TBool | TFun {tFunArg :: Type, tFunRes :: Type} 
  deriving (Eq)
{-@ data Type = TTUnit | TBool | TFun {tFunArg :: Type, tFunRes :: Type} @-}


data Sub = Sub {subVar :: Var, subTerm :: Term}
{-@ data Sub = Sub {subVar :: Var, subTerm :: Term} @-}

-------------------------------------------------------------------------------
-- | Evaluation ---------------------------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect eval @-}
{-@ eval :: Term -> Term @-}
eval :: Term -> Term
eval (TIF TTrue  t2 _)     = t2 
eval (TIF TFalse _ t3)     = t3
eval (TIF t1 t2 t3)        = TIF (eval t1) t2 t3
eval (TFix (TLam x t))     = subst (Sub x (TFix (TLam x t))) t
eval (TFix t)              = TFix (eval t)
eval (TApp (TLam x t1) t2) = subst (Sub x t2) t1
eval (TApp t1 t2)          = TApp (eval t1) t2
eval v                     = v 

-------------------------------------------------------------------------------
-- | Substitution -------------------------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect subst @-}
{-@ subst :: Sub -> t:Term -> Term / [size t] @-}
subst :: Sub -> Term -> Term 
subst (Sub x xt) (TVar y)
  | x == y             = xt 
  | otherwise          = TVar y 
subst _  THole         = THole
subst su (TApp t1 t2)  = TApp (subst su t1) (subst su t2)
subst su (TFix t)      = TFix (subst su t)
subst su (TIF t t1 t2) = TIF (subst su t) (subst su t1) (subst su t2)

subst (Sub x xt) (TLam y e)   
  | x == y              = TLam y e
  | otherwise           = TLam y (subst (Sub x xt) e)
subst _ x               = x   




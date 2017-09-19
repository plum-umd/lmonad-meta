-- type Label = Integer -- JP: Do we need a different type for a partial order?

data Label = 
    LabelAMeetB 
  | LabelA 
  | LabelB 
  | LabelAJoinB
  deriving (Eq)

{-@ data Label = 
    LabelAMeetB 
  | LabelA 
  | LabelB 
  | LabelAJoinB
@-}

{-@ reflect canFlowTo @-}
canFlowTo :: Label -> Label -> Bool
canFlowTo _ LabelAJoinB = True
canFlowTo LabelAJoinB _ = False
canFlowTo LabelA LabelA = True
canFlowTo LabelAMeetB LabelA = True
canFlowTo LabelB LabelA = False
canFlowTo LabelB LabelB = True
canFlowTo LabelAMeetB LabelB = True
canFlowTo LabelA LabelB = False
canFlowTo LabelAMeetB LabelAMeetB = True
canFlowTo LabelA LabelAMeetB = False
canFlowTo LabelB LabelAMeetB = False
-- canFlowTo x y | x == y = True


type Var   = Integer
-------------------------------------------------------------------------------
-- | Terms --------------------------------------------------------------------
-------------------------------------------------------------------------------

-- JP: Separate values from terms?

data Term 
  = THole
  | TLam {lamVar :: Var, lamTerm :: Term}
  | TTrue 
  | TFalse 
  | TUnit 
  | TVar {tVar :: Var}
  | TApp {tApp1 :: Term, tApp2 :: Term}
  | TFix {tFix :: Term}
  | TIf  {tIfCond :: Term, tIfThen :: Term, tIfElse :: Term} 

  | TLabel Label

  | TGetLabel
  | TGetClearance
  | TLowerClearance Term -- JP: Label or Term? Probably term???

  | TException
  deriving Eq 

-- JP: Join, Meet, CanFlowTo...

{-@ data Term [size]
  = THole 
  | TLam {lamVar :: Var, lamTerm :: Term}
  | TTrue 
  | TFalse 
  | TUnit 
  | TVar {tVar :: Var}
  | TApp {tApp1 :: Term, tApp2 :: Term}
  | TFix {tFix :: Term}
  | TIf  {iIfCond :: Term, tIfThen :: Term, tIfElse :: Term} 

  | TLabel Label

  | TGetLabel
  | TGetClearance
  | TLowerClearance Term

  | TException
 @-} 

size :: Term -> Integer 
{-@ measure size @-}
{-@ invariant {t:Term | 0 <= size t} @-}
{-@ size :: Term -> {v:Integer |  0 <= v }  @-}
size (TIf t1 t2 t3) = 1 + size t1 + size t2 + size t3 
size (TFix t)       = 1 + size t 
size (TApp t1 t2)   = 1 + size t1 + size t2 
size THole          = 0
size (TVar _)       = 1 
size (TLam _ e)     = 1 + size e
size TTrue          = 1 
size TFalse         = 1 
size TUnit          = 1 

size (TLabel _)      = 1 -- JP: Is this fine???

size TGetLabel      = 0 -- JP: Is this fine???
size TGetClearance  = 0 -- JP: Is this fine???
size (TLowerClearance t) = 1 + size t

size TException     = 0

isValue :: Term -> Bool 
{-@ measure isValue @-}
isValue (TLam _ _) = True 
isValue TUnit      = True 
isValue TTrue      = True 
isValue TFalse     = True 
isValue (TLabel _) = True 
isValue TException = True
isValue _          = False 


-------------------------------------------------------------------------------
-- | Types --------------------------------------------------------------------
-------------------------------------------------------------------------------

data Type = TTUnit | TBool | TFun {tFunArg :: Type, tFunRes :: Type} 
  deriving (Eq)
{-@ data Type = TTUnit | TBool | TFun {tFunArg :: Type, tFunRes :: Type} @-}
-- TODO: exceptions


data Sub = Sub {subVar :: Var, subTerm :: Term}
{-@ data Sub = Sub {subVar :: Var, subTerm :: Term} @-}

-------------------------------------------------------------------------------
-- | Evaluation ---------------------------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect eval @-}
{-@ eval :: Term -> Term @-}
eval :: Term -> Term
-- eval t | propagateException t = TException
eval t | hasException t    = TException
eval (TIf TTrue  t2 _)     = t2 
eval (TIf TFalse _ t3)     = t3
eval (TIf t1 t2 t3)        = TIf (eval t1) t2 t3
eval (TFix (TLam x t))     = subst (Sub x (TFix (TLam x t))) t
eval (TFix t)              = TFix (eval t)
eval (TApp (TLam x t1) t2) = subst (Sub x t2) t1
eval (TApp t1 t2)          = TApp (eval t1) t2

eval (TLowerClearance t)   = TLowerClearance (eval t)
-- eval v | isValue v         = v 
-- TGetLabel, TLowerClearance, and TGetClearance are unreachable?
eval v                     = v 

-- NV: Should that be recursively deinfed? 
{-@ reflect hasException @-}
hasException :: Term -> Bool 
hasException (TLam _ TException)          = True
hasException (TLam _ _)                   = False
hasException (TApp TException _)          = True
hasException (TApp _ TException)          = True
hasException (TApp _ _)                   = False
hasException (TFix TException)            = True
hasException (TFix _)                     = False
hasException (TIf TException _ _)         = True
hasException (TIf _ TException _)         = True
hasException (TIf _ _ TException)         = True
hasException (TIf _ _ _)                  = False
hasException (TLowerClearance TException) = True
hasException (TLowerClearance _)          = False
hasException TException                   = True

hasException THole = False
hasException TTrue = False
hasException TFalse = False
hasException TUnit = False
hasException (TVar _) = False
hasException (TLabel _) = False
hasException TGetLabel = False
hasException TGetClearance = False
-- hasException _                            = False 


-- Propagate exceptions first.
-- {-@ reflect propagateException @-}
-- {-@ propagateException :: Term -> Bool @-}
-- propagateException :: Term -> Bool
-- propagateException _ = False
-- 
-- propagateException THole = False
-- propagateException (TLam _ t) = propagateException t
-- propagateException TTrue = False
-- propagateException TFalse = False
-- propagateException TUnit = False
-- propagateException (TVar _) = False
-- propagateException (TApp t1 t2) = propagateException t1 || propagateException t2
-- propagateException (TFix t1) = propagateException t1
-- propagateException (TIf t1 t2 t3) = propagateException t1 || propagateException t2 || propagateException t3
-- 
-- propagateException (TLabel _) = False
-- 
-- propagateException TGetLabel = False
-- propagateException TGetClearance = False
-- propagateException (TLowerClearance _) = False
-- 
-- propagateException TException = True

-------------------------------------------------------------------------------
-- | Substitution -------------------------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect subst @-}
{-@ subst :: Sub -> t:Term -> Term / [size t] @-}
subst :: Sub -> Term -> Term 
subst (Sub x xt) (TVar y)
  | x == y             = xt 
  | otherwise          = TVar y 
subst (Sub x xt) (TLam y e)   
  | x == y             = TLam y e
  | otherwise          = TLam y (subst (Sub x xt) e)

subst _  THole         = THole
subst su (TApp t1 t2)  = TApp (subst su t1) (subst su t2)
subst su (TFix t)      = TFix (subst su t)
subst su (TIf t t1 t2) = TIf (subst su t) (subst su t1) (subst su t2)
subst _  x             = x 

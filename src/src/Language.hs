{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}
{-@ LIQUID "--trustinternals"                           @-}

module Language where

-- type Label = Integer -- JP: Do we need a different type for a partial order?

data Label = 
    LabelAMeetB 
  | LabelA 
  | LabelB 
  | LabelAJoinB
  deriving (Eq, Show)

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

{-@ reflect join @-}
join :: Label -> Label -> Label
join LabelAJoinB _ = LabelAJoinB
join _ LabelAJoinB = LabelAJoinB
join LabelA LabelB = LabelAJoinB
join LabelA LabelA = LabelA
join LabelA LabelAMeetB = LabelA
join LabelB LabelA = LabelAJoinB
join LabelB LabelB = LabelB
join LabelB LabelAMeetB = LabelB
join LabelAMeetB LabelA = LabelA
join LabelAMeetB LabelB = LabelB
join LabelAMeetB LabelAMeetB = LabelAMeetB

{-@ reflect meet @-}
meet :: Label -> Label -> Label
meet LabelAMeetB _ = LabelAMeetB
meet _ LabelAMeetB = LabelAMeetB
meet LabelA LabelB = LabelAMeetB
meet LabelA LabelA = LabelA
meet LabelA LabelAJoinB = LabelA
meet LabelB LabelA = LabelAMeetB
meet LabelB LabelB = LabelB
meet LabelB LabelAJoinB = LabelB
meet LabelAJoinB v = v

{-@ reflect boolToTerm @-}
boolToTerm :: Bool -> Term
boolToTerm True  = TTrue
boolToTerm False = TFalse


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
  | TJoin {tJoin1 :: Term, tJoin2 :: Term}
  | TMeet {tMeet1 :: Term, tMeet2 :: Term}
  | TCanFlowTo {tCanFlowTo1 :: Term, tCanFlowTo2 :: Term}

  | TBind {tBind1 :: Term, tBind2 :: Term}
  -- JP: Omitting return for now. Maybe not needed.

  | TGetLabel
  | TGetClearance
  | TLowerClearance Term

  | TLabeledTCB Label Term
  | TLabelOf Term
  | TUnlabel Term

  | TException
  deriving (Eq, Show)

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
  | TJoin {tJoin1 :: Term, tJoin2 :: Term}
  | TMeet {tMeet1 :: Term, tMeet2 :: Term}
  | TCanFlowTo {tCanFlowTo1 :: Term, tCanFlowTo2 :: Term}

  | TBind {tBind1 :: Term, tBind2 :: Term}

  | TGetLabel
  | TGetClearance
  | TLowerClearance Term

  | TLabeledTCB Label Term
  | TLabelOf Term
  | TUnlabel Term

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

size (TLabel _)     = 1 -- JP: Is this fine???
size (TJoin t1 t2)  = 1 + size t1 + size t2
size (TMeet t1 t2)  = 1 + size t1 + size t2
size (TCanFlowTo t1 t2)  = 1 + size t1 + size t2

size (TBind t1 t2)  = 1 + size t1 + size t2

size TGetLabel      = 0 -- JP: Is this fine???
size TGetClearance  = 0 -- JP: Is this fine???
size (TLowerClearance t) = 1 + size t

size (TLabeledTCB _ t) = 1 + size t
size (TLabelOf t) = 1 + size t
size (TUnlabel t) = 1 + size t

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

eval (TJoin (TLabel l1) (TLabel l2)) = TLabel (join l1 l2)
eval (TJoin (TLabel l1) t2)          = TJoin (TLabel l1) (eval t2)
eval (TJoin t1 t2)                   = TJoin (eval t1) t2

eval (TMeet (TLabel l1) (TLabel l2)) = TLabel (meet l1 l2)
eval (TMeet (TLabel l1) t2)          = TMeet (TLabel l1) (eval t2)
eval (TMeet t1 t2)                   = TMeet (eval t1) t2

eval (TCanFlowTo (TLabel l1) (TLabel l2)) = boolToTerm (canFlowTo l1 l2)
eval (TCanFlowTo (TLabel l1) t2)          = TCanFlowTo (TLabel l1) (eval t2)
eval (TCanFlowTo t1 t2)                   = TCanFlowTo (eval t1) t2

eval THole                                = THole
eval t@(TLam _ _)                         = t
eval t@TTrue                              = t
eval t@TFalse                             = t
eval t@TUnit                              = t
eval t@(TVar _)                           = t

eval t@(TLabel _)                         = t

-- Monadic
eval t@(TBind _ _)                        = t
eval t@TGetLabel                          = t
eval t@TGetClearance                      = t
eval (TLowerClearance t)                  = TLowerClearance (eval t)
eval (TUnlabel t)                         = TUnlabel (eval t)

eval t@(TLabeledTCB _ _)                  = t

eval (TLabelOf (TLabeledTCB l _))         = TLabel l
eval (TLabelOf t)                         = TLabelOf (eval t)

eval t@TException                         = t

-- eval (TLowerClearance t)   = TLowerClearance (eval t)
-- eval v | isValue v         = v 
-- eval v                     = v 

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

hasException (TBind TException _) = True
hasException (TBind _ TException) = True
hasException (TBind _ _) = False

hasException (TLabel _) = False
hasException (TJoin TException _) = True
hasException (TJoin _ TException) = True
hasException (TJoin _ _) = False
hasException (TMeet TException _) = True
hasException (TMeet _ TException) = True
hasException (TMeet _ _) = False
hasException (TCanFlowTo TException _) = True
hasException (TCanFlowTo _ TException) = True
hasException (TCanFlowTo _ _) = False

hasException TGetLabel = False
hasException TGetClearance = False

hasException (TLabeledTCB _ TException) = True -- JP: Do we propagate here?
hasException (TLabeledTCB _ _) = False

hasException (TLabelOf TException) = True
hasException (TLabelOf _) = False

hasException (TUnlabel TException) = True
hasException (TUnlabel _) = False

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
subst _ TTrue         = TTrue
subst _ TFalse        = TFalse
subst _ TUnit         = TUnit
subst _ t@(TLabel _)  = t
subst su (TJoin t1 t2) = TJoin (subst su t1) (subst su t2)
subst su (TMeet t1 t2) = TMeet (subst su t1) (subst su t2)
subst su (TCanFlowTo t1 t2) = TCanFlowTo (subst su t1) (subst su t2)
subst su (TBind t1 t2) = TBind (subst su t1) (subst su t2)
subst _ TGetLabel          = TGetLabel
subst _ TGetClearance        = TGetClearance
subst su (TLowerClearance t) = TLowerClearance (subst su t)

subst _ (TLabeledTCB l t)    = TLabeledTCB l t -- JP: Does it make sense for unbound variables to exist in t??? --  (subst su t)
subst su (TLabelOf t)        = TLabelOf (subst su t)
subst su (TUnlabel t)        = TUnlabel (subst su t)

subst _ TException           = TException
-- subst _  x             = x 

{-@ LIQUID "--exactdc"                                  @-}
{-@ LIQUID "--higherorder"                              @-}

module Language where

import Label 

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

  | TVLabel Label
  | TJoin {tJoin1 :: Term, tJoin2 :: Term}
  | TMeet {tMeet1 :: Term, tMeet2 :: Term}
  | TCanFlowTo {tCanFlowTo1 :: Term, tCanFlowTo2 :: Term}

  | TBind {tBind1 :: Term, tBind2 :: Term}
  -- JP: Omitting return for now. Maybe not needed.

  | TGetLabel
  | TGetClearance
  | TLowerClearance Term

  | TLabeledTCB {tLabeledLabel :: Label, tLabeledTerm :: Term}
  | TLabelOf Term
  | TLabel {tLabelLabel :: Term, tLabelTerm :: Term}
  | TUnlabel Term

  | TToLabeled {tToLabeledLabel :: Term, tToLabeledTerm :: Term}

  | TException
  deriving (Eq, Show)

-- JP: Join, Meet, CanFlowTo...

{-@ data Term [size] @-}

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

size (TVLabel _)     = 1 -- JP: Is this fine???
size (TJoin t1 t2)  = 1 + size t1 + size t2
size (TMeet t1 t2)  = 1 + size t1 + size t2
size (TCanFlowTo t1 t2)  = 1 + size t1 + size t2

size (TBind t1 t2)  = 1 + size t1 + size t2

size TGetLabel      = 0 -- JP: Is this fine???
size TGetClearance  = 0 -- JP: Is this fine???
size (TLowerClearance t) = 1 + size t

size (TLabeledTCB _ t) = 1 + size t
size (TLabelOf t) = 1 + size t
size (TLabel t1 t2) = 1 + size t1 + size t2
size (TUnlabel t) = 1 + size t

size (TToLabeled t1 t2) = 1 + size t1 + size t2

size TException     = 1

isValue :: Term -> Bool 
{-@ reflect isValue @-}
isValue (TLam _ _)  = True  -- TLam :: _ -> _ -> {v:Term | isValue v}
isValue TUnit       = True  -- TUnit :: {v:Term | isValue v}
isValue TTrue       = True 
isValue TFalse      = True 
isValue (TVLabel _) = True 
isValue TException  = True
isValue _           = False 

-- JP: TLabeledTCB _ t if isValue t ?


-------------------------------------------------------------------------------
-- | Types --------------------------------------------------------------------
-------------------------------------------------------------------------------

data Type = TTUnit | TBool | TFun {tFunArg :: Type, tFunRes :: Type} 
  deriving (Eq)

data Sub = Sub {subVar :: Var, subTerm :: Term}
{-@ data Sub = Sub {subVar :: Var, subTerm :: Term} @-}

-------------------------------------------------------------------------------
-- | Evaluation ---------------------------------------------------------------
-------------------------------------------------------------------------------

{-@ reflect eval @-}
{-@ eval :: Term -> Term @-}
eval :: Term -> Term
eval t | propagateException t    = TException
eval (TIf TTrue  t2 _)     = t2 
eval (TIf TFalse _ t3)     = t3
eval (TIf t1 t2 t3)        = TIf (eval t1) t2 t3
eval (TFix (TLam x t))     = subst (Sub x (TFix (TLam x t))) t
eval (TFix t)              = TFix (eval t)
eval (TApp (TLam x t1) t2) = subst (Sub x t2) t1
eval (TApp t1 t2)          = TApp (eval t1) t2

eval (TJoin (TVLabel l1) (TVLabel l2)) = TVLabel (join l1 l2)
eval (TJoin (TVLabel l1) t2)          = TJoin (TVLabel l1) (eval t2)
eval (TJoin t1 t2)                   = TJoin (eval t1) t2

eval (TMeet (TVLabel l1) (TVLabel l2)) = TVLabel (meet l1 l2)
eval (TMeet (TVLabel l1) t2)          = TMeet (TVLabel l1) (eval t2)
eval (TMeet t1 t2)                   = TMeet (eval t1) t2

eval (TCanFlowTo (TVLabel l1) (TVLabel l2)) = boolToTerm (canFlowTo l1 l2)
eval (TCanFlowTo (TVLabel l1) t2)           = TCanFlowTo (TVLabel l1) (eval t2)
eval (TCanFlowTo t1 t2)                     = TCanFlowTo (eval t1) t2

eval THole                                = THole
eval t@(TLam _ _)                         = t
eval t@TTrue                              = t
eval t@TFalse                             = t
eval t@TUnit                              = t
eval t@(TVar _)                           = t

eval t@(TVLabel _)                        = t

-- Monadic
eval t@(TBind _ _)                        = t
eval t@TGetLabel                          = t
eval t@TGetClearance                      = t
eval (TLowerClearance t)                  = TLowerClearance (eval t)
eval (TUnlabel t)                         = TUnlabel (eval t)
eval (TLabel l@(TVLabel _) t2)            = TLabel l (eval t2)
eval (TLabel t1 t2)                       = TLabel (eval t1) t2

eval t@(TLabeledTCB _ _)                  = t

eval (TLabelOf (TLabeledTCB l _))         = TVLabel l
eval (TLabelOf t)                         = TLabelOf (eval t)

eval (TToLabeled l@(TVLabel _) t)         = TToLabeled l (eval t)
eval (TToLabeled t1 t2)                   = TToLabeled (eval t1) t2

eval t@TException                         = t

-- eval (TLowerClearance t)   = TLowerClearance (eval t)
-- eval v | isValue v         = v 
-- eval v                     = v 

{-@ measure propagateException @-}
propagateException :: Term -> Bool 

propagateException TException          = True

propagateException THole               = False
propagateException TTrue               = False
propagateException TFalse              = False
propagateException TUnit               = False
propagateException (TVar _)            = False
propagateException (TVLabel _)         = False
propagateException TGetLabel           = False
propagateException TGetClearance       = False
-- propagateException (TLabeledTCB _ TException) = True -- JP: Do we propagate here?
propagateException (TLabeledTCB _ _)   = False

{- 
propagateException (TLam _ e)          = e  == TException 
propagateException (TApp e1 e2)        = e1 == TException || e2 == TException 
propagateException (TFix e)            = e  == TException 
propagateException (TIf e e1 e2)       = e  == TException || e1 == TException || e2 == TException 
propagateException (TLowerClearance e) = e  == TException
propagateException (TBind e1 e2)       = e1 == TException || e2 == TException  
propagateException (TJoin e1 e2)       = e1 == TException || e2 == TException 
propagateException (TMeet e1 e2)       = e1 == TException || e2 == TException 
propagateException (TCanFlowTo e1 e2)  = e1 == TException || e2 == TException 
propagateException (TLabelOf e)        = e  == TException 
propagateException (TLabel e1 e2)      = e1 == TException || e2 == TException  
propagateException (TUnlabel e)        = e  == TException 
propagateException (TToLabeled e1 e2)  = e1 == TException || e2 == TException  
-}

propagateException (TLam _ e)          = propagateException e 
propagateException (TApp e1 e2)        = propagateException e1 || propagateException e2 
propagateException (TFix e)            = propagateException e 
propagateException (TIf e e1 e2)       = propagateException e  || propagateException e1 || propagateException e2
propagateException (TLowerClearance e) = propagateException e 
propagateException (TBind e1 e2)       = propagateException e1 || propagateException e2 
propagateException (TJoin e1 e2)       = propagateException e1 || propagateException e2 
propagateException (TMeet e1 e2)       = propagateException e1 || propagateException e2 
propagateException (TCanFlowTo e1 e2)  = propagateException e1 || propagateException e2 
propagateException (TLabelOf e)        = propagateException e 
propagateException (TLabel e1 e2)      = propagateException e1 || propagateException e2 
propagateException (TUnlabel e)        = propagateException e 
propagateException (TToLabeled e1 _e2)  = propagateException e1
    -- || propagateException e2 


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
subst _ t@(TVLabel _)  = t
subst su (TJoin t1 t2) = TJoin (subst su t1) (subst su t2)
subst su (TMeet t1 t2) = TMeet (subst su t1) (subst su t2)
subst su (TCanFlowTo t1 t2) = TCanFlowTo (subst su t1) (subst su t2)
subst su (TBind t1 t2) = TBind (subst su t1) (subst su t2)
subst _ TGetLabel          = TGetLabel
subst _ TGetClearance        = TGetClearance
subst su (TLowerClearance t) = TLowerClearance (subst su t)

subst _ (TLabeledTCB l t)    = TLabeledTCB l t -- JP: Does it make sense for unbound variables to exist in t??? --  (subst su t)
subst su (TLabelOf t)        = TLabelOf (subst su t)
subst su (TLabel t1 t2)      = TLabel (subst su t1) (subst su t2)
subst su (TUnlabel t)        = TUnlabel (subst su t)

subst su (TToLabeled t1 t2)        = TToLabeled (subst su t1) (subst su t2)

subst _ TException           = TException
-- subst _  x             = x 


-------------------------------------------------------------------------------
-- Predicates ----------------------------------------------------------------
-------------------------------------------------------------------------------

{-@ measure isTLam @-}
isTLam :: Term -> Bool 
isTLam (TLam _ _) = True 
isTLam _          = False 

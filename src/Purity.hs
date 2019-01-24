{-@ LIQUID "--reflection"  @-}

module Purity where

import ProofCombinators 
import Programs
import Labels 
import Prelude hiding (Maybe(..), fromJust, isJust)

{-@ pureProp
  :: (Eq l, Label l) 
  => l:l 
  -> db:DB l 
  -> t:{Term l | isPure t } 
  -> { eval (Pg l db t) = Pg l db (evalTerm t) } @-} 
pureProp  :: (Eq l, Label l) => l -> DB l -> Term l -> Proof 
pureProp l db t@(TLabeled _ _) = eval (Pg l db t) ==. Pg l db (evalTerm t)*** QED 
pureProp l db t@(TInt _)       = eval (Pg l db t) ==. Pg l db (evalTerm t)*** QED
pureProp l db t@TUnit          = eval (Pg l db t) ==. Pg l db (evalTerm t)*** QED
pureProp l db t@THole          = eval (Pg l db t) ==. Pg l db (evalTerm t)*** QED
pureProp l db t@TException     = eval (Pg l db t) ==. Pg l db (evalTerm t)*** QED
pureProp l db t@(TPred _)      = eval (Pg l db t) ==. Pg l db (evalTerm t)*** QED
pureProp l db t@TNil           = eval (Pg l db t) ==. Pg l db (evalTerm t)*** QED
pureProp l db t@(TCons _ _)    = eval (Pg l db t) ==. Pg l db (evalTerm t)*** QED
pureProp l db t@TTrue          = eval (Pg l db t) ==. Pg l db (evalTerm t)*** QED
pureProp l db t@TFalse         = eval (Pg l db t) ==. Pg l db (evalTerm t)*** QED
pureProp l db t@(TIf _ _ _)    = eval (Pg l db t) ==. Pg l db (evalTerm t)*** QED
pureProp l db t@(TApp _ _)     = eval (Pg l db t) ==. Pg l db (evalTerm t)*** QED
pureProp l db t@(TLam _ _)     = eval (Pg l db t) ==. Pg l db (evalTerm t)*** QED
pureProp l db t@(TVar _ )      = eval (Pg l db t) ==. Pg l db (evalTerm t)*** QED
pureProp l db t@(TVLabel _)    = eval (Pg l db t) ==. Pg l db (evalTerm t)*** QED
pureProp l db t@(TJust _)      = eval (Pg l db t) ==. Pg l db (evalTerm t)*** QED
pureProp l db t@TNothing       = eval (Pg l db t) ==. Pg l db (evalTerm t)*** QED
pureProp l db t@(TCase _ _ _ ) = eval (Pg l db t) ==. Pg l db (evalTerm t)*** QED
pureProp _ _  t                = assert (not (isPure t))

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE IncoherentInstances   #-}

module ProofCombinators (

  -- Attention! the operators Admitted and (==?) are 
  -- UNSAFE: they should not belong the final proof term

  -- * Proof is just a () alias 
  Proof
  
  -- * Proof constructors 
  , trivial, unreachable, (***), QED(..)

  -- * Proof certificate constructors
  , (?)

  -- * These two operators check all intermediate equalities 
  , (==!) -- proof of equality is implicit eg. x ==! y
  , (==:) -- proof of equality is explitic eg. x ==: y ? p

  -- Uncheck operator used only for proof debugging
  
  , (==?) -- x ==? y always succeds 
  , admitted -- always succeds 

  -- * The below operator does not check intermediate equalities
  --   but takes optional proof argument.
  , (==.)

  -- * Combining Proofs 
  , (&&&)

) where

-------------------------------------------------------------------------------
-- | Proof is just a () alias -------------------------------------------------
-------------------------------------------------------------------------------

type Proof = ()

-------------------------------------------------------------------------------
-- | Proof Construction -------------------------------------------------------
-------------------------------------------------------------------------------

-- | trivial is proof by SMT

trivial :: Proof
trivial =  ()

-- {-@ unreachable :: {v : Proof | False } @-}
unreachable :: Proof
unreachable =  ()

{-@ assume admitted :: {v : Proof | False} @-}
admitted :: Proof
admitted = ()

-- All proof terms are deleted at runtime.
{- RULE "proofs are irrelevant" forall (p :: Proof). p = () #-}

-- | proof casting 
-- | `x *** QED`: x is a proof certificate* strong enough for SMT to prove your theorem
-- | `x *** Admitted`: x is an unfinished proof

infixl 3 *** 
{-@ assume (***) :: a -> p:QED -> { if (isAdmitted p) then false else true } @-}
(***) :: a -> QED -> Proof 
_ *** _ = ()

data QED = Admitted | QED    

{-@ measure isAdmitted :: QED -> Bool @-}
{-@ Admitted :: {v:QED | isAdmitted v } @-}


-------------------------------------------------------------------------------
-- | * Checked Proof Certificates ---------------------------------------------
-------------------------------------------------------------------------------

-- Any (refined) carries proof certificates. 
-- For example 42 :: {v:Int | v == 42} is a certificate that 
-- the value 42 is equal to 42. 
-- But, this certificate will not really be used to proof any fancy theorems.

-- Below we provide a number of equational operations
-- that constuct proof certificates. 

-- | Implicit equality

-- x ==! y returns the proof certificate that 
-- result value is equal to both x and y
-- when y == x (as assumed by the operator's precondition) 

infixl 3 ==!
{-@ (==!) :: x:a -> y:{a | y == x} -> {v:a | v == x && v == y} @-} 
(==!) :: a -> a -> a 
x ==! _  = x

-- | Explicit equality
-- `x ==: y ? p` returns the proof certificate that 
-- result value is equal to both x and y
-- when y == x is explicitely asserted by the proof term p

infixl 3 ==:
{-@ (==:) :: x:a -> y:a -> {v:Proof | x == y} -> {v:a | v == x && v == y} @-} 
(==:) :: a -> a -> Proof -> a 
(==:) x _ _ = x

-- where `?` is basically Haskell's $ and is used for the right precedence

infixl 3 ?
(?) :: (Proof -> a) -> Proof -> a
f ? y = f y


-- | Assumed equality
-- `x ==? y ` returns the admitted proof certificate that 
-- result value is equal to both x and y

infixl 3 ==?
{-@ assume (==?) :: x:a -> y:a -> {v:a | v == x && v == y} @-} 
(==?) :: a -> a -> a 
(==?) x _ = x


-- Example: See ListExamples 

-- In short: 
-- - (==?) is only for proof debuging
-- - (==:) requires explicit proof term
-- - (==!) does not require explicit proof term

-------------------------------------------------------------------------------
-- | * Unchecked Proof Certificates -------------------------------------------
-------------------------------------------------------------------------------

-- The above operators check each intermediate proof step.
-- The operator `==.` below accepts an optional proof term 
-- argument, but does not check intermediate steps.

infixl 3 ==.

class OptEq a r where
  (==.) :: a -> a -> r

instance (a~b) => OptEq a (Proof -> b) where
{-@ instance OptEq a (Proof -> b) where
  ==. :: x:a -> y:a -> {v:Proof | x == y} -> {v:b | v ~~ x && v ~~ y}
  @-}
  (==.) x _ _ = x

instance (a~b) => OptEq a b where
{-@ instance OptEq a b where
  ==. :: x:a -> y:{a| x == y} -> {v:b | v ~~ x && v ~~ y }
  @-}
  (==.) x _ = x

-------------------------------------------------------------------------------
-- | * Combining Proof Certificates -------------------------------------------
-------------------------------------------------------------------------------


(&&&) :: Proof -> Proof -> Proof
x &&& _ = x 

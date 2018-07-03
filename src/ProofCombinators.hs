module ProofCombinators where 

-- {-@ reflect assert @-}
assert :: Bool -> Proof 
{-@ assert :: b:{Bool | b} -> {v:Proof | b} @-}
assert _ = () 


use :: a -> Proof 
use _ = () 

{-@ impl :: x:Bool -> y:Bool -> {v:Bool | v <=> (x => y)} @-} 
impl :: Bool -> Bool -> Bool 
impl a b = if a then b else True

{-@ iff :: x:Bool -> y:Bool -> {v:Bool | v <=> (x <=> y)} @-} 
iff :: Bool -> Bool -> Bool 
iff a b = (if a then b else True) && if b then a else True 


assume :: Bool -> Proof 
{-@ assume assume :: b:Bool -> {v:Proof | b} @-}
assume _ = ()

type Proof = ()


-- | p *** QED casts p into a proof 

data QED = QED 

infixl 2 ***
x *** QED = ()


-------------------------------------------------------------------------------
-- | Equational Reasoning -----------------------------------------------------
-------------------------------------------------------------------------------

-- use (==.) not to check intermediate steps 

infixl 3 ==.

(==.) :: a -> a -> a 
_ ==. x = x 
{-# INLINE (==.) #-} 

infixl 2 =>.

(=>.) :: Bool -> Bool -> Bool 
_ =>. x = x 
{-# INLINE (=>.) #-} 


infixl 2 <=.

(<=.) :: Bool -> Bool -> Bool 
_ <=. x = x 
{-# INLINE (<=.) #-} 

-- Explanations: embed a proof into a term

infixl 3 ?
(?) :: a -> Proof -> a 
x ? _ = x 
{-# INLINE (?)   #-} 

(&&&) :: Proof -> Proof -> Proof
x &&& _ = x  


infixl 3 =/=
{-@ assume (=/=) :: x:a -> y:{a| x /= y } -> {v:a | v == x && v == y} @-} 
(=/=) :: a -> a -> a 
x =/= _  = x


infixl 3 ==?
{-@ assume (==?) :: x:a -> y:a -> {v:a | v == x && v == y} @-} 
(==?) :: a -> a -> a 
x ==? _  = x

infixl 3 ==!
{-@ (==!) :: x:a -> y:{a | y == x} -> {v:a | v == x && v == y} @-} 
(==!) :: a -> a -> a 
x ==! _  = x


infixl 4 ==:
{-@ (==:) :: x:a -> y:a -> {v:Proof | x == y} -> {v:a | v == x && v == y} @-} 
(==:) :: a -> a -> Proof -> a 
(==:) x _ _ = x

{-@ reflect cast @-}
{-@ cast :: b -> x:a -> {v:a | v == x } @-}
cast :: a -> b -> b 
cast _ y = y 

-- {-@ measure cast :: b -> a -> a @-}
-- {-@ cast :: b -> x:a -> {v:a | v == x } @-}
-- cast :: b -> a -> a
-- cast _ x = x

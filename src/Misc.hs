module Misc where

infixl 3 ==??
{-@ (==??) :: x:a -> y:{a | y == x} -> {v:a | v == x && v == y} @-} 
(==??) :: a -> a -> a 
x ==?? _  = x

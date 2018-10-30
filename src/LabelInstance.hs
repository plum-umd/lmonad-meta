{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}

module LabelInstance where

import ProofCombinators
data Label = Low | Medium | High 
  deriving (Eq, Show)

low, high :: Label
low  = Low 
high = High

{-@ reflect canFlowTo @-}
canFlowTo :: Label -> Label -> Bool
canFlowTo Low High  = True 
canFlowTo Low Medium  = True 
canFlowTo Low Low   = True
canFlowTo High High = True 
canFlowTo High Medium = False
canFlowTo High Low  = False 
canFlowTo Medium High = True 
canFlowTo Medium Medium = True 
canFlowTo Medium Low  = False 

{-@ reflect meet @-}
meet :: Label -> Label -> Label 
meet a b = if a `canFlowTo` b then a else b

-- meet Low High  = Low 
-- meet Low Low   = Low
-- meet High High = High 
-- meet High Low  = Low 

{-@ reflect join @-}
join :: Label -> Label -> Label 
join a b = if a `canFlowTo` b then b else a

-- join Low High  = High 
-- join Low Low   = Low
-- join High High = High 
-- join High Low  = High 

{-@ reflect bot @-}
bot :: Label 
bot = Low


{-@ lawBot:: l:Label -> { canFlowTo bot l} @-}
lawBot Low  = () 
lawBot High = () 

{-@ lawFlowReflexivity:: l:Label -> { canFlowTo l l} @-}
lawFlowReflexivity :: Label -> Proof 
lawFlowReflexivity _      = ()


{-@ lawFlowAntisymmetry :: a:Label -> b:{Label | canFlowTo a b && canFlowTo b a} -> { a == b } @-}
lawFlowAntisymmetry :: Label -> Label -> ()
lawFlowAntisymmetry _ _   = () 


{-@ lawFlowTransitivity :: a:Label -> b:Label -> c:Label 
  -> {(canFlowTo a b && canFlowTo b c) => canFlowTo a c} @-}
lawFlowTransitivity :: Label -> Label -> Label -> ()
lawFlowTransitivity _ _ _ = () 


{-@ ple lawMeet @-}
{-@ lawMeet :: z:Label -> x:Label -> y:Label -> w:Label 
  -> { z == meet x y => (canFlowTo z x && canFlowTo z y && ((canFlowTo w x && canFlowTo w y) => canFlowTo w z))} @-}
lawMeet :: Label -> Label -> Label -> Label -> () 

lawMeet Low  Low  Low  Low  = ()
lawMeet Low  Low  Low  High = ()
lawMeet Low  Low  High Low  = ()
lawMeet Low  Low  High High = ()
lawMeet Low  High Low  Low  = ()
lawMeet Low  High Low  High = ()
lawMeet Low  High High Low  = ()
lawMeet Low  High High High = ()
lawMeet High Low  Low  Low  = ()
lawMeet High Low  Low  High = ()
lawMeet High Low  High Low  = ()
lawMeet High Low  High High = ()
lawMeet High High Low  Low  = ()
lawMeet High High Low  High = ()
lawMeet High High High Low  = ()
lawMeet High High High High = ()


{-@ ple lawJoin @-}
{-@ lawJoin :: z:Label -> x:Label -> y:Label -> w:Label 
  -> { z == join x y => (canFlowTo x z && canFlowTo y z && ((canFlowTo x w && canFlowTo y w) => canFlowTo z w))} @-}
lawJoin :: Label -> Label -> Label -> Label -> () 
lawJoin Low  Low  Low  Low  = ()
lawJoin Low  Low  Low  High = ()
lawJoin Low  Low  High Low  = ()
lawJoin Low  Low  High High = ()
lawJoin Low  High Low  Low  = ()
lawJoin Low  High Low  High = ()
lawJoin Low  High High Low  = ()
lawJoin Low  High High High = ()
lawJoin High Low  Low  Low  = ()
lawJoin High Low  Low  High = ()
lawJoin High Low  High Low  = ()
lawJoin High Low  High High = ()
lawJoin High High Low  Low  = ()
lawJoin High High Low  High = ()
lawJoin High High High Low  = ()
lawJoin High High High High = ()

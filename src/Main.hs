{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module Main where

import Labels
import qualified LabelInstance as LI
import LabelInstance (low, high)
import Programs 

import Prelude hiding (Just)


main :: IO () 
main = do
    putStrLn "p = "
    putStrLn $ show $ pgUp'
    putStrLn $ show $ checkSimulations low pgUp'


{- FIXED  
    putStrLn "p = "
    putStrLn $ show $ pgUp
    putStrLn $ show $ checkSimulations low pgUp
    putStrLn "\n WHY? Let εp = ε low p"
    putStrLn "\t Both p and εp are allowed to update the first field"
    putStrLn "\t BUT εp is allowed to update the second field, but p is not"
    putStrLn "\t So εp updates both fields, but p updates none"
    putStrLn "\t Simulations fails because the difference in the first field is observed..."

    putStrLn "\nDUALLY\n"



    putStrLn "p = "
    putStrLn $ show $ pgUp2
    putStrLn $ show $ checkSimulations low pgUp2

    putStrLn "\n WHY? Let εp = ε low p"
    putStrLn "\t Both p and εp are allowed to update the first field"
    putStrLn "\t BUT p is allowed to update the second field, but εp is not"
    putStrLn "\t So p updates both fields, but εp updates none"
    putStrLn "\t Simulations fails because the difference in the first field is observed..."


    let l = low
    putStrLn "p2!"
    putStrLn $ show $ pg1
    putStrLn $ show $ eval pg1
    putStrLn $ show $ ε l $ eval pg1
    putStrLn "p1!"
    putStrLn $ show $ pg2
    putStrLn $ show $ eval pg2
    putStrLn $ show $ ε l $ eval pg2
    putStrLn $ show $ checkNonInferference l pg1 pg2
-}

checkNonInferference :: (Eq l, Label l) => l -> Program l -> Program l -> Bool 
checkNonInferference l p1 p2 
  = if ε l p1 == ε l p2 && ς p1 && ς p2 
      then ε l (eval p1) == ε l (eval p2)
      else error "not low equivalent"


-- FAILING: checkSimulations low pgUp

checkSimulations :: (Eq l, Label l) => l -> Program l -> Bool 
checkSimulations l p 
  = if ς p 
      then ε l (eval p) == ε l (eval (ε l p))
      else error "assumption broken"

--- Update Failing Example: checkSimulations low pgUp

-- l = low
-- This example run with l = low presents why we need to raise with the label table
-- basically, if table label cannot flow to l, then the erased always succeds
-- the non erased might throw an expection or not, depending on whether the 
-- table is empty or not. 
pgUp' :: Program LI.Label
pgUp' = Pg low dbUp2' termUp'

dbUp2' :: DB LI.Label
dbUp2' = [Pair tname1 (Table tinfoUp' [Row (TInt 3) (TInt 32) (TInt 42)])]
tinfoUp' :: TInfo LI.Label
tinfoUp' = TInfo high {-!!!-} low low (Fun low []) 1
termUp' :: Term LI.Label 
termUp' = TUpdate tname1 (TPred (Pred0 True)) (TLabeled low (TInt 42)) (TLabeled high (TInt 42))


pgUp2 :: Program LI.Label
pgUp2 = Pg low dbUp2 termUp

dbUp2 :: DB LI.Label
dbUp2 = [Pair tname1 (Table tinfoUp [Row (TInt 3) (TInt 32) (TInt 42)])]

tinfoUp2 :: TInfo LI.Label
tinfoUp2 = TInfo low low high (Fun low []) 1



pgUp :: Program LI.Label
pgUp = Pg low dbUp termUp

dbUp :: DB LI.Label
dbUp = [Pair tname1 (Table tinfoUp [Row (TInt 3) (TInt 32) THole])]

termUp :: Term LI.Label 
termUp = TUpdate tname1 (TPred (Pred0 True)) (TLabeled low (TInt 42)) (TLabeled high (TInt 42))
tinfoUp :: TInfo LI.Label
tinfoUp = TInfo low low low (Fun low []) 1


-------------------------------------------------------------------------------
-- | Testing update -----------------------------------------------------------
-------------------------------------------------------------------------------

dbCheck :: Program LI.Label -> Bool 
dbCheck (Pg lc db (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2)))   
  | Just t <- lookupTable n db 
  =  updateLabelCheck lc t p l1 v1 l2 v2 
dbCheck (Pg lc db (TUpdate n (TPred p) (TLabeled l1 v1) (TLabeled l2 v2)))   
  | _ <- lookupTable n db 
  = error "Not Found"
dbCheck _   
  = error "Bad Input"




pg1 :: Program LI.Label
pg1 = Pg low db (term TTrue)
pg2 :: Program LI.Label
pg2 = Pg low db (term TFalse)
tname1 :: TName 
tname1 = TName 1 
tinfo1 :: TInfo LI.Label
tinfo1 = TInfo low low low (Fun low []) 1


db :: DB LI.Label
db = [Pair tname1 (Table tinfo1 [Row (TInt 3) (TInt 32) (TInt 6)])]
term :: Term LI.Label -> Term LI.Label 
term v = 
  let t = TBind (TUnlabel (TLabeled high v)) 
          (TLam secret (
            TIf (TVar secret) 
              (TDelete tname1 (TPred (Pred0 True))) 
              (TReturn TUnit)
          ))
  in
  -- let t = TReturn TUnit in
  -- TBind (TToLabeled (TVLabel High) t) (TLam x (TSelect tname1 (TPred (Pred False False False))))
  TBind (TToLabeled (TVLabel high) t) (TLam x (TReturn TUnit))
  where
   secret = "secret"
   x = "x"


-------------------------------------------------------------------------------
-- | Labels -------------------------------------------------------------------
-------------------------------------------------------------------------------

instance Label LI.Label where 
  canFlowTo = LI.canFlowTo
  meet      = LI.meet 
  join      = LI.join
  bot       = LI.bot 

  lawBot    = LI.lawBot
  lawFlowReflexivity  = LI.lawFlowReflexivity
  lawFlowAntisymmetry = LI.lawFlowAntisymmetry
  lawFlowTransitivity = LI.lawFlowTransitivity

  lawMeet = LI.lawMeet
  lawJoin = LI.lawJoin

-------------------------------------------------------------------------------
-- | Printing -----------------------------------------------------------------
-------------------------------------------------------------------------------


instance Show l => Show (Program l) where 
  show (PgHole _)  = "PgHole"
  show (Pg l db t) = "<" ++ show l ++ ", " ++ "..." ++ ", " ++ show t ++ ">"

deriving instance Show l => Show (Term    l)
deriving instance Show l => Show (Table   l)
deriving instance Show l => Show (TInfo   l)
deriving instance Show l => Show (Row     l)
deriving instance Eq l   => Eq (Program l)
deriving instance Show l => Show (Fun (Term l) l)

instance Show (Pred l) where 
  show _ = "Pred!!!"

instance (Show a, Show b) => Show (Pair a b) where 
  show (Pair x y) = "(" ++ show x ++ "," ++ show y ++ ")"

instance Show TName where
  show (TName x) = show x 






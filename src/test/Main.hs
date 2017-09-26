module Main where

import Language
import Programs

main :: IO ()
main = do
    run 5 p0

    run 4 p1
    
    putStrLn "Done"

run 0 _ = putStrLn ""
run n p = evalPrint p >>= run (n - 1)

evalPrint p = do
    putStrLn $ show p
    let (Pair _ p') = evalProgram p
    return p'

-- v <- getClearance
-- if v `canFlowTo` LabelAJoinB then
--   v1
-- else
--   v2
p0 = 
    let vL = 63 in
    let tC = TCanFlowTo (TVar vL) $ TVLabel LabelAJoinB in
    let t = TBind TGetClearance $ TLam vL $ TIf tC (TVar 1) (TVar 0) in
    Pg LabelA LabelA Memory t
    

-- x <- toLabeled LabelA TException
-- unlabel x
p1 = 
    let v = 63 in
    let ttl = TToLabeled (TVLabel LabelA) TException in

    Pg LabelA LabelA Memory $ TBind ttl (TLam v (TUnlabel (TVar v)))


-- 1: (\l . label l "x") LabelA
-- 2: (\l . label l "y") LabelA
-- equiv = do
--     let t x = TLab l $ TLabel
--     let p0 = Pg LabelA LabelA Memory 

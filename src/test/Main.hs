module Main where

import Language
import Programs

main :: IO ()
main = do
    let tC = TCanFlowTo TGetClearance $ TLabel LabelAJoinB
    let t = TIf tC (TVar 1) (TVar 0)
    let p0 = Pg LabelA LabelA Memory t
    putStrLn $ show p0
    
    let (Pair _ p1) = evalProgram p0
    putStrLn $ show p1

    let (Pair _ p2) = evalProgram p1
    putStrLn $ show p2

    putStrLn "Done"

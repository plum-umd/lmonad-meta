module Main where

import Language
import Programs

main :: IO ()
main = do
    let vL = 63
    let tC = TCanFlowTo (TVar vL) $ TLabel LabelAJoinB
    let t = TBind TGetClearance $ TLam vL $ TIf tC (TVar 1) (TVar 0)
    let p0 = Pg LabelA LabelA Memory t
    putStrLn $ show p0

    evalPrint p0 >>= evalPrint >>= evalPrint >>= evalPrint

    -- equiv
    
    putStrLn "Done"

evalPrint p = do
    let (Pair _ p') = evalProgram p
    putStrLn $ show p'
    return p'


-- 1: (\l . label l "x") LabelA
-- 2: (\l . label l "y") LabelA
-- equiv = do
--     let t x = TLab l $ TLabel
--     let p0 = Pg LabelA LabelA Memory 

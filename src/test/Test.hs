module Main where

import System.Exit
import System.Process

main :: IO ()
main = do 
  c1 <- runCommand' ("cd " ++ sourceDir)
  runLiquid "Label.hs"

runLiquid :: String -> IO ExitCode
runLiquid fname = runCommand' ("stack exec -- liquid " ++ fname)

sourceDir :: String
sourceDir = "src/src"

runCommand' :: String -> IO ExitCode
runCommand' str = 
  do ps <- runCommand str -- (str ++ "> log 2>&1")
     ec <- waitForProcess ps 
     putStrLn ("\nCommand `" ++ str ++ "` exited with " ++ show ec)
     return ec
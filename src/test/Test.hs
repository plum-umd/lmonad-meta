{-# LANGUAGE BangPatterns #-}

module Main where

import System.Exit
import System.Process

main :: IO ExitCode
main = runAllLiquid


runAllLiquid :: IO ExitCode
runAllLiquid = mconcat <$> mapM runLiquid orderedSrcFiles  


orderedSrcFiles :: [String]
orderedSrcFiles = [
    "Misc.hs"
  , "Label.hs"
  , "Language.hs"
  , "Programs.hs"
  , "MetaFunctions.hs"
  , "Simulations/Language.hs"
{- 
  , "Simulations/MetaFunctions.hs"
  , "Simulations/Programs.hs"
  , "Simulations.hs"
  , "Determinacy.hs"
  , "LLIO.hs"
-}
  ]

runLiquid :: String -> IO ExitCode
runLiquid fname 
  = runCommand' ("cd " ++ sourceDir ++ "; stack exec -- liquid " ++ fname)

sourceDir :: String
sourceDir = "src"

runCommand' :: String -> IO ExitCode
runCommand' str = 
  do ps <- runCommand (str ++ "> log 2>&1")
     ec <- waitForProcess ps 
     putStrLn ("\nCommand `" ++ str ++ "` exited with " ++ show ec)
     return ec


instance Monoid ExitCode where
  mempty = ExitSuccess
  mappend (ExitFailure i) _ = ExitFailure i 
  mappend ExitSuccess e     = e 

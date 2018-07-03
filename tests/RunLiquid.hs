{-# LANGUAGE BangPatterns #-}

module RunLiquid where

import System.Exit
import System.Process

liquid :: [String] -> IO ()
liquid files 
  = runCommand' "cd db && make clean" >> runAllLiquid files >>= exitWith


definitions :: [String]
definitions = [
    "ProofCombinators.hs"
  , "Labels.hs"
  , "Predicates.hs"
  , "Programs.hs"
  ]

runAllLiquid :: [String] -> IO ExitCode
runAllLiquid files = mconcat <$> mapM runLiquid (definitions ++ files) 

runLiquid :: String -> IO ExitCode
runLiquid fname 
  = runCommand' ("cd db && stack exec -- liquid " ++ fname)

runCommand' :: String -> IO ExitCode
runCommand' str = 
  do ps <- runCommand str 
     ec <- waitForProcess ps 
     putStrLn ("\nCommand `" ++ str ++ "` exited with " ++ show ec)
     return ec


instance Monoid ExitCode where
  mempty = ExitSuccess
  mappend (ExitFailure i) _ = ExitFailure i 
  mappend ExitSuccess e     = e 
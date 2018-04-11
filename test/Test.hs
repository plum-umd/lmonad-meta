{-# LANGUAGE BangPatterns #-}

module Main where

import Control.Monad
import System.Exit
import System.Process

main :: IO ()
main = runAllLiquid >>= exitWith

runAllLiquid :: IO ExitCode
runAllLiquid = mconcat <$> mapM runLiquid orderedSrcFiles  

orderedSrcFiles :: [String]
orderedSrcFiles = [
    "Misc.hs"
  , "Label.hs"
  , "Language.hs"
  , "Programs.hs"
  , "MetaFunctions.hs"
  , "Termination.hs"
  , "Simulations/Language.hs"
  , "Simulations/MetaFunctions.hs"
  , "Simulations/Helpers.hs"
  , "Simulations/Programs.hs"
  , "Simulations/EraseSubErase.hs"
  , "Simulations/EraseEvalErase.hs"
  , "Simulations.hs"
  , "Determinacy.hs"
  , "LLIO.hs"
  ]

runLiquid :: String -> IO ExitCode
runLiquid fname 
  = runCommand' ("stack exec -- liquid " ++ fname)

runCommand' :: String -> IO ExitCode
runCommand' str = 
  do ps <- runCommand str -- (str ++ "> log 2>&1")
     ec <- waitForProcess ps 
     putStrLn ("\nCommand `" ++ str ++ "` exited with " ++ show ec)
     when (ec /= ExitSuccess) $ 
        runCommand "cat log" >>= waitForProcess >> return ()
     return ec


instance Monoid ExitCode where
  mempty = ExitSuccess
  mappend (ExitFailure i) _ = ExitFailure i 
  mappend ExitSuccess e     = e 

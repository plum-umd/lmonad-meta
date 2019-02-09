{-# LANGUAGE BangPatterns #-}

module Main where

import RunLiquid

main :: IO ()
main = liquid [
    "EraseTableAny.hs"
  , "LabelUpdateCheck.hs"
  , "Simulations/UpdateAny.hs"
  , "Simulations/UpdateRowBySMT.hs"
  , "Simulations/UpdateOne.hs"
  , "Simulations/Update.hs"
  , "Simulations/TUpdateFound.hs"
  , "Simulations/UpdateAnyNothingJust.hs"
  , "Simulations/TUpdate.hs"
  ]

{-# LANGUAGE BangPatterns #-}

module Main where

import RunLiquid

main :: IO ()
main = liquid [
    "EraseTableAny.hs"
  , "LabelUpdateCheck.hs"
  , "LabelUpdateCheckNothingJust.hs"
  , "Simulations/UpdateAny.hs"
  , "Simulations/UpdateAnyNothingJust.hs"
  , "Simulations/UpdateRowBySMT.hs"
  , "Simulations/UpdateOne.hs"
  , "Simulations/UpdateOneNothingJust.hs"
  , "Simulations/Update.hs"
  , "Simulations/UpdateNothingJust.hs"
  , "Simulations/TUpdateFound.hs"
  , "Simulations/TUpdateFoundNothingJust.hs"
  , "Simulations/TUpdate.hs"
  ]

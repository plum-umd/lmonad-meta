{-# LANGUAGE BangPatterns #-}

module Main where

import RunLiquid

main :: IO ()
main = liquid [
    "Simulations/DeleteAll.hs"
  , "Simulations/DeleteHelpers.hs"
  , "Simulations/TDeleteFound.hs"
  , "Simulations/Delete.hs"
  , "Simulations/TDeletePgHole.hs"
  , "Simulations/TDelete.hs"
  ]

{-# LANGUAGE BangPatterns #-}

module Main where

import RunLiquid

main :: IO ()
main = liquid [
    "Simulations/Simulations.hs"
  , "NonInterference.hs"
  ]

module Main where

import RunLiquid  

main :: IO ()
main = liquid  [
    "Simulations/TToLabeledTVLabel.hs"
  , "Simulations/TToLabeled.hs"
  ]


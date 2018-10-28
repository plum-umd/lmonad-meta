module Main where

import RunLiquid  

main :: IO ()
main = liquid  [
    "DBValueErase.hs"
  , "Simulations/TToLabeledTVLabel.hs"
  , "Simulations/TToLabeled.hs"
  ]


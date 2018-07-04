{-# LANGUAGE BangPatterns #-}

module Main where

import RunLiquid

main :: IO ()
main = liquid [
    "LabelSelectTable.hs"
  , "LabelSelectErase.hs"
  , "Simulations/Select.hs"
  , "Simulations/TSelect.hs"
  ]

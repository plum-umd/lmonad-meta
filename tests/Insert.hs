{-# LANGUAGE BangPatterns #-}

module Main where

import RunLiquid

main :: IO ()
main = liquid [
    "Simulations/Insert.hs"
  , "Simulations/InsertAny.hs"
  , "Simulations/TInsertPgHole.hs"
  , "Simulations/TInsert0.hs"
  , "Simulations/TInsert.hs"
  ]


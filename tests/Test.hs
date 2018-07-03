{-# LANGUAGE BangPatterns #-}

module Main where

import RunLiquid

main :: IO ()
main = liquid [
  -- General Theorems
    "Monotonicity.hs"
  , "Idempotence.hs"
  , "HomomorphicSubst.hs"
  , "TableInfoErase.hs"
  , "DBValueErase.hs"
  , "Purity.hs"
  , "SafeErase.hs"
  , "SafeDBValues.hs"
  
  , "LabelPredImplies.hs"
  , "LookupTableErase.hs"
  , "LabelPredErase.hs"
  , "LabelPredEraseEqual.hs"

  -- Specific Simulations 
  , "Simulations/Terms.hs"
  , "Simulations/Pure.hs"
  , "Simulations/Predicates.hs"

  -- Simulations 
  , "Simulations/Simulations.hs"

  -- Finally, 
  , "NonInterference.hs"
  ]


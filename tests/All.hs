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

  -- ToLabeled 
  , "Simulations/TToLabeledTVLabel.hs"
  , "Simulations/TToLabeled.hs"

  -- Delete

  , "Simulations/DeleteAll.hs"
  , "Simulations/DeleteHelpers.hs"
  , "Simulations/TDeleteFound.hs"
  , "Simulations/Delete.hs"
  , "Simulations/TDeletePgHole.hs"
  , "Simulations/TDelete.hs"

  -- Insert 
  , "Simulations/Insert.hs"
  , "Simulations/InsertAny.hs"
  , "Simulations/TInsertPgHole.hs"
  , "Simulations/TInsert0.hs"
  , "Simulations/TInsert.hs"

  -- Select 
  , "LabelSelectTable.hs"
  , "LabelSelectErase.hs"
  , "Simulations/Select.hs"
  , "Simulations/TSelect.hs"

  -- Update 
  , "EraseTableAny.hs"
  , "LabelUpdateCheck.hs"
  , "Simulations/UpdateAny.hs"
  , "Simulations/UpdateRowBySMT.hs"
  , "Simulations/UpdateOne.hs"
  , "Simulations/Update.hs"
  , "Simulations/TUpdateFound.hs"
  , "Simulations/TUpdate.hs"

  -- Simulations 
  , "Simulations/Simulations.hs"

  -- Finally, 
  , "NonInterference.hs"
  ]


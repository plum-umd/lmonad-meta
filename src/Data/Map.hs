{-# LANGUAGE NoImplicitPrelude #-}

module Data.Map where

import GHC.Types
import Prelude hiding (lookup)

-- import Data.List hiding (lookup)

-- import Data.Eq
-- import Data.Bool
-- import Data.Int
-- import qualified Data.List as List
-- import Data.Maybe

newtype Map a b = Map [(a,b)]

{-@ reflect lookup @-}
lookup :: Eq k => k -> [(k,v)] -> Maybe v
lookup x [] = Nothing
lookup x ((k,v):kvs)
  | x == k       = Just v
  | True         = lookup x kvs

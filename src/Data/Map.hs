{-@ LIQUID "--exactdc"                                  @-}

{- LANGUAGE NoImplicitPrelude #-}

module Data.Map where

-- import GHC.Types
import Prelude hiding (lookup)

-- import Data.List hiding (lookup)

-- import Data.Eq
-- import Data.Bool
-- import Data.Int
-- import qualified Data.List as List
-- import Data.Maybe

newtype Map a b = Map [(a,b)]
    deriving (Eq, Show)
    -- TODO: This Eq is wrong XXX

{-@ reflect lookup @-}
lookup :: Eq k => k -> Map k v -> Maybe v
lookup x (Map []) = Nothing
lookup x (Map ((k,v):kvs))
  | x == k       = Just v
  | True         = lookup x (Map kvs)

empty :: Map a b
empty = Map []

lookupMax :: Map k v -> Maybe (k,v)
lookupMax = undefined

foldl :: (a -> b -> a) -> a -> Map k b -> a
foldl = undefined

foldlWithKey :: (a -> k -> b -> a) -> a -> Map k b -> a
foldlWithKey = undefined

insert :: Ord k => k -> a -> Map k a -> Map k a
insert = undefined

fromList :: Ord k => [(k, a)] -> Map k a
fromList = undefined

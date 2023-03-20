{-# Language DerivingStrategies #-}
{-# Language OverloadedStrings #-}
{-# Language Safe #-}

module Thesis.Catalog.Option
    ( Option (..)
    , completeSetOfOptions
    ) where

import Data.Set (Set, fromList)


data  Option
    = UseMinimizedDFA
    | MaxMemoryAllocs
    | MaxVectorLength


deriving stock instance Bounded Option


deriving stock instance Enum Option


deriving stock instance Eq Option


deriving stock instance Ord Option


deriving stock instance Show Option


completeSetOfOptions :: Set Option
completeSetOfOptions = fromList [minBound .. maxBound]
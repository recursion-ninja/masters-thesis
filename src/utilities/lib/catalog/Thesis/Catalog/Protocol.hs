{-# Language DerivingStrategies #-}
{-# Language OverloadedStrings #-}
{-# Language Safe #-}

module Thesis.Catalog.Protocol
    ( Protocol (..)
    , completeSetOfProtocolVersions
    ) where

import Data.Ix
import Data.Set (Set, fromList)


data  Protocol
    = Version1
    | Version2


deriving stock instance Bounded Protocol


deriving stock instance Enum Protocol


deriving stock instance Eq Protocol


deriving stock instance Ix Protocol


deriving stock instance Ord Protocol


instance Show Protocol where

    show = ("TreeKEM-v" <>) . \case
        Version1 -> "1.0"
        Version2 -> "2.0"

completeSetOfProtocolVersions :: Set Protocol
completeSetOfProtocolVersions = fromList [ minBound .. maxBound ] 
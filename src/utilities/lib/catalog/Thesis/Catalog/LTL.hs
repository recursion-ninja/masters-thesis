{-# Language DerivingStrategies #-}
{-# Language OverloadedStrings #-}
{-# Language Safe #-}

module Thesis.Catalog.LTL
    ( LTL (..)
    , completeSetOfLTLs
    ) where

import Data.Ix
import Data.Set (Set, fromList)


data  LTL
    = HLT
    | PCS
    | FSU
    | Anything


deriving stock instance Bounded LTL


deriving stock instance Enum LTL


deriving stock instance Eq LTL


deriving stock instance Ix LTL


deriving stock instance Ord LTL


instance Show LTL where

    show = \case
        HLT -> "HLT"
        PCS -> "PCS"
        FSU -> "FSU"
        Anything -> "???"


completeSetOfLTLs :: Set LTL
completeSetOfLTLs = fromList [HLT .. FSU]

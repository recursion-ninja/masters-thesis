{-# Language DeriveAnyClass #-}
{-# Language DerivingStrategies #-}
{-# Language OverloadedStrings #-}
{-# Language Safe #-}
{-# Language UnboxedSums #-}

module Thesis.Catalog.LTL
    ( LTL (..)
    , completeSetOfLTLs
    ) where

import Control.DeepSeq
import Data.Ix
import Data.Set (Set, fromList)
import GHC.Generics (Generic)


data  LTL
    = HLT
    | PCS
    | FSU
    | Anything


deriving stock instance Bounded LTL


deriving stock instance Enum LTL


deriving stock instance Eq LTL


deriving stock instance Generic LTL


deriving stock instance Ix LTL


deriving anyclass instance NFData LTL


deriving stock instance Ord LTL


instance Show LTL where

    show = \case
        HLT -> "HLT"
        PCS -> "PCS"
        FSU -> "FSU"
        Anything -> "???"


completeSetOfLTLs :: Set LTL
completeSetOfLTLs = fromList [HLT .. FSU]

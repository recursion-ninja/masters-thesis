{-# Language DerivingStrategies #-}
{-# Language OverloadedLists #-}
{-# Language OverloadedStrings #-}

module Thesis.Batch.Catalog.LTL
    ( LTL (..)
    , completeSetOfLTLs
    , textualLTL
    ) where

import Data.Map (foldrWithKey, fromSet)
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.String (IsString(..))
import Data.Validation
import Thesis.Batch.Printer.Class
import Thesis.Batch.Scanner.Fault


data  LTL
    = HLT
    | PCS
    | FSU
    | Anything


deriving stock instance Bounded LTL


deriving stock instance Enum LTL


deriving stock instance Eq LTL


deriving stock instance Ord LTL


instance RenderableCellEntry LTL where

    renderCellEntry = t


instance Show LTL where

    show = t


t :: IsString s => LTL -> s
t = \case
    HLT -> "HLT"
    PCS -> "PCS"
    FSU -> "FSU"
    Anything -> "???"


completeSetOfLTLs :: Set LTL
completeSetOfLTLs = [HLT .. FSU]


textualLTL :: forall s . (Eq s, IsString s) => s -> Validation ScanFault LTL
textualLTL txt =
    let opts = fromSet t completeSetOfLTLs

        seek :: a -> s -> Maybe a -> Maybe a
        seek k v a
            | v == txt  = Just k
            | otherwise = a

    in  pure . fromMaybe Anything $ foldrWithKey seek Nothing opts

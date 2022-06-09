{-# Language DerivingStrategies #-}
{-# Language ExistentialQuantification #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language OverloadedLists #-}
{-# Language OverloadedStrings #-}

module Thesis.Batch.Catalog.LTL
    ( LTL ()
    , completeSetOfLTLs
    , textualLTL
    ) where

import Data.Coerce (coerce)
import Data.Set (Set)
import Data.String (IsString(..))
import Data.Text (Text, unpack)
import Data.Text.Builder.Linear (fromText)
import Thesis.Batch.Printer.Class


newtype LTL
    = LTL Text


deriving newtype instance Eq LTL


deriving newtype instance Ord LTL


deriving newtype instance IsString LTL


instance RenderableCellEntry LTL where

    renderCellEntry (LTL txt) = "  " <> fromText txt <> " "


instance Show LTL where

    show = unpack . coerce


completeSetOfLTLs :: Set LTL
completeSetOfLTLs = ["FSU", "HLT", "PCS"]


textualLTL :: Text -> LTL
textualLTL = LTL

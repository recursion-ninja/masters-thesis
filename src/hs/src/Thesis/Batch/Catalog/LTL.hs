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

import Data.Set (Set)
import Data.String (IsString(..))
import Data.Text (Text)
import Data.Text.Builder.Linear (fromText)
import Thesis.Batch.Printer.Class


newtype LTL
    = LTL Text


deriving newtype instance Eq LTL


deriving newtype instance Ord LTL


deriving newtype instance IsString LTL


instance RenderableCell LTL where

    renderCell (LTL txt) = "  " <> fromText txt <> " "


deriving newtype instance Show LTL


completeSetOfLTLs :: Set LTL
completeSetOfLTLs = ["FSU", "HLT", "PCS"]


textualLTL :: Text -> LTL
textualLTL = LTL

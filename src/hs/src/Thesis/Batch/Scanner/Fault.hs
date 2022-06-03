{-# Language GeneralizedNewtypeDeriving #-}

module Thesis.Batch.Scanner.Fault
    ( ScanFault
    , renderScanFault
    , textError
    ) where

import Data.Foldable
import Prelude hiding (unlines)

import Data.List.NonEmpty (NonEmpty(..))
import Data.String (IsString(..))
import Data.Text (Text, unlines, unpack)
import Data.Validation


newtype ScanFault
    = TableErrs (NonEmpty Text)


deriving newtype instance Eq ScanFault


deriving newtype instance Ord ScanFault


deriving newtype instance Semigroup ScanFault


instance Show ScanFault where

    show = unpack . renderScanFault


instance IsString ScanFault where

    fromString = TableErrs . pure . fromString


renderScanFault :: ScanFault -> Text
renderScanFault (TableErrs errs) = unlines $ toList errs


textError :: Text -> Validation ScanFault a
textError = Failure . TableErrs . pure

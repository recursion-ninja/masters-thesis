{-# Language DerivingStrategies #-}
{-# Language OverloadedLists #-}
{-# Language OverloadedStrings #-}
{-# Language ScopedTypeVariables #-}

module Thesis.Batch.Catalog.Option
    ( Option (..)
    , completeSetOfOptions
    , textualOption
    ) where

import Data.Map (foldrWithKey, fromSet)
import Data.Set (Set)
import Data.String (IsString(..))
import Data.Validation
import Thesis.Batch.Printer.Class
import Thesis.Batch.Scanner.Fault


data  Option
    = UseMinimizedDFA
    | MaxMemoryAllocs
    | MaxVectorLength


deriving stock instance Bounded Option


deriving stock instance Enum Option


deriving stock instance Eq Option


deriving stock instance Ord Option


instance RenderableCell Option where

    renderCell UseMinimizedDFA = "DFAMIN"
    renderCell MaxMemoryAllocs = "MEMORY"
    renderCell MaxVectorLength = "VECTOR"


deriving stock instance Show Option


t :: IsString s => Option -> s
t UseMinimizedDFA = "DFAMIN"
t MaxMemoryAllocs = "MEMORY"
t MaxVectorLength = "VECTOR"


completeSetOfOptions :: Set Option
completeSetOfOptions = [minBound .. maxBound]


textualOption :: forall s . (Eq s, IsString s, Show s) => s -> Validation ScanFault Option
textualOption txt =
    let opts = fromSet t completeSetOfOptions

        seek :: a -> s -> Maybe a -> Maybe a
        seek k v a
            | v == txt  = Just k
            | otherwise = a
    in  case foldrWithKey seek Nothing opts of
        Nothing -> textError $ "Unrecognized header: " <> fromString (show txt)
        Just x  -> pure x

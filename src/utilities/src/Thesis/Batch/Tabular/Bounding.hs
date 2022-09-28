{-# Language DerivingStrategies #-}

module Thesis.Batch.Tabular.Bounding
    ( Bounding (..)
    ) where

import Data.Vector.Unboxed (Vector)
import Thesis.Batch.Catalog.Size
import Thesis.Batch.Catalog.Time


data  Bounding a
    = Bounding
    { boundedColIndices      :: Vector Size
    , boundedRowIndices      :: Vector Time
    , boundedTableCellEntrys :: a
    }


deriving stock instance Eq a => Eq (Bounding a)


deriving stock instance Functor Bounding


deriving stock instance Ord a => Ord (Bounding a)


deriving stock instance Show a => Show (Bounding a)

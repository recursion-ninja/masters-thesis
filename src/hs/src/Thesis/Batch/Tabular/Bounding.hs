{-# Language DerivingStrategies #-}

module Thesis.Batch.Tabular.Bounding
    ( Bounding (..)
    ) where

import Data.Vector.Unboxed (Vector)
import Thesis.Batch.Catalog.Parameter


data  Bounding a
    = Bounding
    { boundedColIndices :: Vector Parameter
    , boundedRowIndices :: Vector Parameter
    , boundedTableCells :: a
    }


deriving stock instance Eq a => Eq (Bounding a)


deriving stock instance Functor Bounding


deriving stock instance Ord a => Ord (Bounding a)


deriving stock instance Show a => Show (Bounding a)

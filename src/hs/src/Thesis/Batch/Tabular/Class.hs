{-# Language Safe #-}
{-# Language TypeFamilies #-}

module Thesis.Batch.Tabular.Class
    ( Tabular (..)
    ) where

import Data.Set (Set, cartesianProduct)


class Tabular a where

    type CellData a

    type ColIndex a

    type RowIndex a

    bagIndices :: a -> Set (RowIndex a, ColIndex a)
    bagIndices = cartesianProduct <$> rowIndices <*> colIndices

    colIndices :: a -> Set (ColIndex a)

    rowIndices :: a -> Set (RowIndex a)

    getIndex :: a -> RowIndex a -> ColIndex a -> CellData a

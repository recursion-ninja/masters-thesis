{-# Language Safe #-}
{-# Language TypeFamilies #-}

module Thesis.Batch.Tabular.Class
    ( Tabular (..)
    ) where

import Data.Set (Set, cartesianProduct)


class Tabular a where

    type Index a

    type Value a

    bagIndices :: a -> Set (Index a, Index a)
    bagIndices = cartesianProduct <$> rowIndices <*> colIndices

    colIndices :: a -> Set (Index a)

    rowIndices :: a -> Set (Index a)

    getIndex :: a -> Index a -> Index a -> Value a

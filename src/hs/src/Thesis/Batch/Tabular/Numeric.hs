{-# Language GeneralizedNewtypeDeriving #-}
{-# Language TypeFamilies #-}

module Thesis.Batch.Tabular.Numeric
    ( MarkdownRows
    , NumericTable (..)
    , NumericTableSet (..)
    , collectNumericTable
    , collectionOfLTLs
    ) where

import Data.Foldable
import Data.Ord (comparing)

import Data.List.NonEmpty (NonEmpty(..))
import Data.Map.Strict (Map, keysSet, singleton)
import Data.Matrix.Unboxed (Matrix)
import Data.Matrix.Unboxed qualified as M
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Vector.Unboxed qualified as V

import Text.MMark.Extension (Inline)
import Thesis.Batch.Catalog.LTL
import Thesis.Batch.Catalog.Parameter
import Thesis.Batch.Tabular.Bounding
import Thesis.Batch.Tabular.Cell
import Thesis.Batch.Tabular.Class


newtype NumericTable
    = NumTable { numTable :: (LTL, Cellular) }


newtype NumericTableSet
    = SetTable { numTableSet :: Map LTL Cellular }


type Cellular = Bounding (Matrix Cell)


type MarkdownRows = NonEmpty (NonEmpty (NonEmpty Inline))


deriving newtype instance Eq NumericTable


deriving newtype instance Eq NumericTableSet


instance Ord NumericTable where

    compare (NumTable (x, _)) (NumTable (y, _)) = compare x y


instance Ord NumericTableSet where

    compare = comparing collectionOfLTLs


deriving stock instance Show NumericTableSet


deriving newtype instance Semigroup NumericTableSet


instance Tabular NumericTable where

    type Index NumericTable = Parameter

    type Value NumericTable = Cell

    colIndices = Set.fromDistinctAscList . V.toList . boundedColIndices . snd . numTable

    rowIndices = Set.fromDistinctAscList . V.toList . boundedRowIndices . snd . numTable

    getIndex m row col =
        let cells = boundedTableCells . snd . numTable
            notes = fold ["Indexing error at ( ", show row, ",", show col, " )"]
        in  fromMaybe (error notes) $ do
            i <- V.elemIndex row . boundedRowIndices . snd $ numTable m
            j <- V.elemIndex col . boundedColIndices . snd $ numTable m
            pure $ M.unsafeIndex (cells m) (i, j)


collectNumericTable :: NumericTable -> NumericTableSet
collectNumericTable = SetTable . uncurry singleton . numTable


collectionOfLTLs :: NumericTableSet -> Set LTL
collectionOfLTLs = keysSet . numTableSet

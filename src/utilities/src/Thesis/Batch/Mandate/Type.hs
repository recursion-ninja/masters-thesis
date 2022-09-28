{-# Language DerivingStrategies #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language OverloadedStrings #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeFamilies #-}

module Thesis.Batch.Mandate.Type
    ( BatchMandate (..)
    , Parameterized
    , Specification
      -- * Queries
    , cardinality
    , codomain
    , domain
    , fulfills
    , queryMandate
    ) where

import Data.Coerce
import Data.Foldable
import Data.List (intersperse)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Matrix.Unboxed (Matrix, flatten, toLists, unsafeIndex)
import Data.Maybe (fromMaybe)
import Data.Set (Set, fromDistinctAscList)
import Data.Text (Text)
import Data.Text.Builder.Linear (Builder)
import Data.Vector (Vector)
import Data.Vector qualified as V
import Data.Vector.Unboxed qualified as VU
import Thesis.Batch.Catalog
import Thesis.Batch.Catalog.Option
import Thesis.Batch.Catalog.Size
import Thesis.Batch.Catalog.Time
import Thesis.Batch.Printer
import Thesis.Batch.Tabular
import Thesis.Batch.Tabular.CellEntry


newtype BatchMandate
    = Batch { unMandate :: WrappedBundle }


type WrappedBundle = Bounding (Map LTL (Matrix Specification))


type Parameterized = (LTL, Time, Size)


type Specification = (UseDFA, CellEntry, CellEntry)


deriving newtype instance Eq BatchMandate


instance RenderableStream BatchMandate where

    renderMarkdown (Batch bounding) =
        let wrappedMap = boundedTableCellEntrys bounding
            otherToken = "T⨉N" :: Text

            toMarkdown :: RenderableCellEntry c => Maybe LTL -> [[c]] -> Builder
            toMarkdown tokenMay =
                let performRendering
                        :: (RenderableCellEntry c, RenderableCellEntry t)
                        => t
                        -> [[c]]
                        -> Builder
                    performRendering corner = renderTable
                        delimiterMarkdown
                        capFirstMarkdown
                        conjoinerMarkdown
                        capFinalMarkdown
                        seperatorMarkdownDefault
                        corner
                        (VU.toList $ boundedColIndices bounding)
                        (VU.toList $ boundedRowIndices bounding)
                in  case tokenMay of
                        Just ltl | ltl `elem` completeSetOfLTLs -> performRendering ltl
                        _ -> performRendering otherToken


            emitTable :: RenderableCellEntry c => Maybe LTL -> [[c]] -> [Builder]
            emitTable k = pure . toMarkdown k

            emitHeader :: RenderableCellEntry h => h -> Builder
            emitHeader c = fold ["### " <> renderCellEntry c, "\n\n"]
        in  fold $ intersperse
            "\n\n\n"
            [ fold . (emitHeader UseMinimizedDFA :) . intersperse "\n\n" $ Map.foldMapWithKey
                (\k -> emitTable (Just k) . fmap (fmap (\(x, _, _) -> x)) . toLists)
                wrappedMap
            , fold . (emitHeader MaxMemoryAllocs :) . intersperse "\n\n" $ Map.foldMapWithKey
                (\k -> emitTable (Just k) . fmap (fmap (\(_, x, _) -> x)) . toLists)
                wrappedMap
            , fold
            . (emitHeader MaxVectorLength :)
            . emitTable Nothing
            . fmap (fmap (\(_, _, x) -> x))
            . toLists
            . snd
            $ Map.findMin wrappedMap
            ]

    renderUnicode = mempty


deriving stock instance Show BatchMandate


instance Tabular BatchMandate where

    type CellEntryData BatchMandate = Map LTL Specification

    type ColIndex BatchMandate = Size

    type RowIndex BatchMandate = Time

    colIndices = fromDistinctAscList . VU.toList . boundedColIndices . unMandate

    rowIndices = fromDistinctAscList . VU.toList . boundedRowIndices . unMandate

    getIndex m row col =
        let props = boundedTableCellEntrys $ unMandate m
            notes = fold ["Indexing error at ( ", show row, ",", show col, " )"]
        in  fromMaybe (error notes) $ do
            i <- VU.elemIndex row . boundedRowIndices $ unMandate m
            j <- VU.elemIndex col . boundedColIndices $ unMandate m
            pure $ (`unsafeIndex` (i, j)) <$> props


queryMandate :: BatchMandate -> Parameterized -> Maybe Specification
queryMandate (Batch mandate) (prop, row, col) = do
    i <- VU.elemIndex row $ boundedRowIndices mandate
    j <- VU.elemIndex col $ boundedColIndices mandate
    m <- Map.lookup prop $ boundedTableCellEntrys mandate
    pure $ unsafeIndex m (i, j)


cardinality :: BatchMandate -> Word
cardinality (Batch bounding) = product $ fmap
    toEnum
    [ length $ boundedTableCellEntrys bounding
    , VU.length $ boundedRowIndices bounding
    , VU.length $ boundedColIndices bounding
    ]


codomain :: BatchMandate -> VU.Vector Specification
codomain = foldMap flatten . boundedTableCellEntrys . (coerce :: BatchMandate -> WrappedBundle)


domain :: BatchMandate -> Set Parameterized
domain (Batch bounding) =
    fromDistinctAscList
        $   (,,)
        <$> Map.keys (boundedTableCellEntrys bounding)
        <*> VU.toList (boundedRowIndices bounding)
        <*> VU.toList (boundedColIndices bounding)


fulfills :: Applicative f => (Parameterized -> Specification -> f a) -> BatchMandate -> f (Vector a)
fulfills f m =
    let n = fromEnum $ cardinality m
        p = V.fromListN n . toList $ domain m
        s = codomain m
        g = f <$> V.unsafeIndex p <*> VU.unsafeIndex s
    in  sequenceA $ V.generate n g

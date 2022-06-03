{-# Language DerivingStrategies #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language OverloadedStrings #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeFamilies #-}

module Thesis.Batch.Mandate.Type
    ( BatchMandate (..)
    , Specification
    , queryMandate
    ) where

import Data.Foldable
import Data.List (intersperse)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Matrix.Unboxed (Matrix, toLists, unsafeIndex)
import Data.Maybe (fromMaybe)
import Data.Set (fromDistinctAscList)
import Data.Text.Builder.Linear (Builder)
import Data.Vector.Unboxed qualified as V
import Thesis.Batch.Catalog
import Thesis.Batch.Catalog.Option
import Thesis.Batch.Printer
import Thesis.Batch.Tabular
import Thesis.Batch.Tabular.Cell


newtype BatchMandate
    = Batch { unMandate :: Bounding (Map LTL (Matrix Specification)) }

                          -- Time ,  Size
--type Parameterized = (LTL, Parameter, Parameter)


type Specification = (UseDFA, Cell, Cell)


deriving newtype instance Eq BatchMandate


instance RenderableStream BatchMandate where

    renderMarkdown (Batch bounding) =
        let mapping    = boundedTableCells bounding
            otherToken = "T⨉N"

            toMarkdown :: RenderableCell c => LTL -> [[c]] -> Builder
            toMarkdown token =
                let corner
                        | token `elem` completeSetOfLTLs = token
                        | otherwise                      = otherToken
                in  renderTable
                        delimiterMarkdown
                        capFirstMarkdown
                        conjoinerMarkdown
                        capFinalMarkdown
                        seperatorMarkdownDefault
                        corner
                        (V.toList $ boundedColIndices bounding)
                        (V.toList $ boundedRowIndices bounding)

            emitTable :: RenderableCell c => LTL -> [[c]] -> [Builder]
            emitTable k = pure . toMarkdown k

            emitHeader :: RenderableCell h => h -> Builder
            emitHeader c = fold ["### " <> renderCell c, "\n\n"]
        in  fold $ intersperse
            "\n\n\n"
            [ fold . (emitHeader UseMinimizedDFA :) . intersperse "\n\n" $ Map.foldMapWithKey
                (\k -> emitTable k . fmap (fmap (\(x, _, _) -> x)) . toLists)
                mapping
            , fold . (emitHeader MaxMemoryAllocs :) . intersperse "\n\n" $ Map.foldMapWithKey
                (\k -> emitTable k . fmap (fmap (\(_, x, _) -> x)) . toLists)
                mapping
            , fold
            . (emitHeader MaxVectorLength :)
            . emitTable otherToken
            . fmap (fmap (\(_, _, x) -> x))
            . toLists
            . snd
            $ Map.findMin mapping
            ]

    renderUnicode = mempty


deriving stock instance Show BatchMandate


instance Tabular BatchMandate where

    type Index BatchMandate = Parameter

    type Value BatchMandate = Map LTL Specification

    colIndices = fromDistinctAscList . V.toList . boundedColIndices . unMandate

    rowIndices = fromDistinctAscList . V.toList . boundedRowIndices . unMandate

    getIndex m row col =
        let props = boundedTableCells $ unMandate m
            notes = fold ["Indexing error at ( ", show row, ",", show col, " )"]
        in  fromMaybe (error notes) $ do
            i <- V.elemIndex row . boundedRowIndices $ unMandate m
            j <- V.elemIndex col . boundedColIndices $ unMandate m
            pure $ specifyVector . (`unsafeIndex` (i, j)) <$> props


queryMandate :: BatchMandate -> LTL -> Parameter -> Parameter -> Maybe Specification
queryMandate (Batch mandate) prop row col = do
    i <- V.elemIndex row $ boundedRowIndices mandate
    j <- V.elemIndex col $ boundedColIndices mandate
    m <- Map.lookup prop $ boundedTableCells mandate
    pure . specifyVector $ unsafeIndex m (i, j)


specifyVector :: (UseDFA, Cell, Cell) -> Specification
specifyVector = id

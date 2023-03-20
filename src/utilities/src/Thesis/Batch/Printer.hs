{-# Language OverloadedStrings #-}
{-# Language Trustworthy #-}

module Thesis.Batch.Printer
    ( -- * Type-class for tabular rendering
      RenderableCellEntry (..)
    , renderTable
      -- * Rendering components
    , capFinalMarkdown
    , capFirstMarkdown
    , conjoinerMarkdown
    , conjoinerUnicode
    , delimiterMarkdown
    , delimiterUnicode
    , seperatorMarkdownCenter
    , seperatorMarkdownDefault
    , seperatorMarkdownLeft
    , seperatorMarkdownRight
    , seperatorUnicode
      -- * Type-class for stream rendering
    , RenderableStream (..)
    ) where

import Data.Foldable (fold)
import Data.Functor (($>))
import Data.List (intersperse)
import Data.Text.Builder.Linear (Builder, fromChar, fromText)
import Thesis.Batch.Printer.Class


delimiterUnicode, conjoinerUnicode, seperatorUnicode :: Builder
delimiterMarkdown, conjoinerMarkdown, capFirstMarkdown, capFinalMarkdown :: Builder
seperatorMarkdownCenter, seperatorMarkdownDefault, seperatorMarkdownLeft, seperatorMarkdownRight :: Builder


delimiterUnicode = fromText " │ "
conjoinerUnicode = fromText " ┼ "
seperatorUnicode = fromText "──────"
delimiterMarkdown = fromText " | "
capFirstMarkdown = fromText " |:"
capFinalMarkdown = fromText ":| "
conjoinerMarkdown = fromText ":|:"
seperatorMarkdownCenter = fromText ":----:"
seperatorMarkdownDefault = fromText "------"
seperatorMarkdownLeft = fromText ":-----"
seperatorMarkdownRight = fromText "-----:"


renderTable
    :: (RenderableCellEntry a, RenderableCellEntry b, RenderableCellEntry c, RenderableCellEntry d)
    => Builder
    -> Builder
    -> Builder
    -> Builder
    -> Builder
    -> a   -- ^ Corner
    -> [b] -- ^ Columns
    -> [c] -- ^ Rows
    -> [[d]] -- ^ CellEntrys
    -> Builder
renderTable delimiter capFirst conjoiner capFinal seperator corner columnTags rowTags cells =
    let lineBreak = fromChar '\n'

        renderVec :: Monoid c => c -> c -> c -> [c] -> c
        renderVec x y z = fold . (<> [z]) . (x :) . intersperse y

        renderRow :: (Functor f, RenderableCellEntry e) => f e -> f Builder
        renderRow = fmap renderCellEntry

        headerRow = renderCellEntry corner : renderRow columnTags
        barredRow = headerRow $> seperator
        tableRows = zipWith (:) (renderRow rowTags) $ renderRow <$> cells

        aboveRows =
            [ renderVec delimiter delimiter delimiter headerRow
            , renderVec capFirst  conjoiner capFinal  barredRow
            ]
        belowRows = renderVec delimiter delimiter delimiter <$> tableRows
    in  renderVec mempty lineBreak mempty $ aboveRows <> belowRows

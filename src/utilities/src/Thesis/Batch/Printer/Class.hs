{-# Language Trustworthy #-}

module Thesis.Batch.Printer.Class
    ( -- * Type-class for tabular rendering
      RenderableCellEntry (..)
      -- * Type-class for stream rendering
    , RenderableStream (..)
      -- * Type-class for choice rendering
    , RenderableChoice (..)
    ) where

import Data.Text.Builder.Linear (Builder, fromText)
import Data.Text (Text)


class RenderableStream a where

    renderMarkdown :: a -> Builder

    renderUnicode :: a -> Builder


class RenderableCellEntry a where

    renderCellEntry :: a -> Builder


class RenderableChoice a where

    renderChoiceName :: a -> Builder

    renderChoiceNote :: a -> Builder

    renderChoiceUnit :: a -> Builder


instance RenderableCellEntry Text where

    renderCellEntry = fromText



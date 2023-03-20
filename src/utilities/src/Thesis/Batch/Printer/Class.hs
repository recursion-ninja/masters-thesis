{-# Language OverloadedStrings #-}
{-# Language Strict #-}
{-# Language Trustworthy #-}

module Thesis.Batch.Printer.Class
    ( -- * Type-class for tabular rendering
      RenderableCellEntry (..)
      -- * Type-class for stream rendering
    , RenderableStream (..)
      -- * Type-class for choice rendering
    , RenderableChoice (..)
    ) where

import Data.String (IsString(fromString))
import Data.Text.Builder.Linear (Builder, fromDec, fromText)
import Data.Text (Text)
import Thesis.Catalog
import Thesis.Catalog.Option
import Thesis.Catalog.Time


class RenderableStream a where

    renderMarkdown :: a -> Builder

    renderUnicode :: a -> Builder


class RenderableCellEntry a where

    renderCellEntry :: a -> Builder


class RenderableChoice a where

    renderChoiceName :: a -> Builder

    renderChoiceNote :: a -> Builder

    renderChoiceUnit :: a -> Builder


instance RenderableCellEntry LTL where

    renderCellEntry = fromString . show


instance RenderableCellEntry Option where

    renderCellEntry UseMinimizedDFA = "DFAMIN"
    renderCellEntry MaxMemoryAllocs = "MEMORY"
    renderCellEntry MaxVectorLength = "VECTOR"


instance RenderableCellEntry Parameter where

    renderCellEntry = renderPad 6


instance RenderableCellEntry Size where

    renderCellEntry = renderPad 6


instance RenderableCellEntry Text where

    renderCellEntry = fromText


instance RenderableCellEntry Time where

    renderCellEntry = renderPad 6


instance RenderableCellEntry UseDFA where

    renderCellEntry bv
        | useDFA bv = "   ⊤  "
        | otherwise = "   ⊥  "


instance RenderableChoice Parameter where

    renderChoiceName = const "Param"

    renderChoiceNote = renderPad 6

    renderChoiceUnit = const " Nat "


instance RenderableChoice Size where

    renderChoiceName = const "Param"

    renderChoiceNote = renderPad 6

    renderChoiceUnit = const " Nat "


instance RenderableChoice Time where

    renderChoiceName = const "Param"

    renderChoiceNote = renderPad 6

    renderChoiceUnit = const " Nat "


instance RenderableChoice UseDFA where

    renderChoiceName = const $ fromText "DFAMIN"

    renderChoiceNote bv
        | useDFA bv = "  YES "
        | otherwise = "  NAY "

    renderChoiceUnit = const $ fromText "Binary"


renderPad :: Enum e => Int -> e -> Builder
renderPad i e =
    let w = fromEnum e
        n = length $ show w
        p = replicate (i - n - 2) ' '
    in  fromString p <> fromDec w <> "  "
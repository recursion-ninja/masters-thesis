{-# Language GeneralizedNewtypeDeriving #-}
{-# Language OverloadedStrings #-}
{-# Language Strict #-}
{-# Language TypeFamilies #-}

module Thesis.Batch.Tabular.CellEntry
    ( CellEntry ()
    ) where

import Control.Applicative ((<|>))
import Control.Monad (when)
import Data.Coerce
import Data.Foldable (fold)
import Data.Set (Set)
import Data.String (IsString(fromString))
import Data.Text.Builder.Linear (Builder, fromDec)
import Data.Vector.Generic qualified as VG
import Data.Vector.Generic.Mutable qualified as VM
import Data.Vector.Primitive qualified as VP
import Data.Vector.Unboxed (Unbox)
import Data.Vector.Unboxed qualified as VU
import GHC.Exts (IsList(fromList))
import Numeric.Natural
import Text.Read
import Thesis.Batch.Printer.Class


newtype CellEntry
    = CellEntry Word


newtype instance VU.MVector s CellEntry = MV_CellEntry (VP.MVector s Word)


newtype instance VU.Vector    CellEntry = V_CellEntry  (VP.Vector    Word)


instance Bounded CellEntry where

    minBound = CellEntry 0

    maxBound = CellEntry 983040


deriving newtype instance Enum CellEntry


deriving newtype instance Eq CellEntry


deriving newtype instance Ord CellEntry


instance RenderableCellEntry CellEntry where

    renderCellEntry (CellEntry w) = renderPad 6 w


instance RenderableChoice CellEntry where

    renderChoiceName = const " CellEntry "

    renderChoiceNote = renderCellEntry

    renderChoiceUnit = const " Byte "


instance Show CellEntry where

    show (CellEntry w) = show w


instance Read CellEntry where

    {-# INLINABLE readPrec #-}
    readPrec =
        let (CellEntry v) = maxBound
            maxValue      = fromIntegral v :: Natural
            vWord         = do
                nat <- readPrec
                when (nat > maxValue) . fail $ fold
                    ["Value '", show nat, "' is greater than maxBound '", show v, "'"]
                pure . CellEntry $ fromIntegral nat

            vBool = do
                c <- get
                if c `elem` (fromList "tTyY⊤" :: Set Char)
                    then pure $ CellEntry 1
                    else if c `elem` (fromList "fFnN⊥" :: Set Char)
                        then pure $ CellEntry 0
                        else fail $ fold ["Unexpected value '", show c, "' found in table cell"]
        in  vBool <|> vWord

    readListPrec = readListPrecDefault


deriving newtype instance Unbox CellEntry


instance VM.MVector VU.MVector CellEntry where

    {-# INLINE basicLength #-}
    basicLength (MV_CellEntry v) = VM.basicLength v

    {-# INLINE basicUnsafeSlice #-}
    basicUnsafeSlice i n (MV_CellEntry v) = MV_CellEntry $ VM.basicUnsafeSlice i n v

    {-# INLINE basicOverlaps #-}
    basicOverlaps (MV_CellEntry v1) (MV_CellEntry v2) = VM.basicOverlaps v1 v2

    {-# INLINE basicUnsafeNew #-}
    basicUnsafeNew n = MV_CellEntry <$> VM.basicUnsafeNew n

    {-# INLINE basicInitialize #-}
    basicInitialize (MV_CellEntry v) = VM.basicInitialize v

    {-# INLINE basicUnsafeReplicate #-}
    basicUnsafeReplicate n x = MV_CellEntry <$> VM.basicUnsafeReplicate n (coerce x)

    {-# INLINE basicUnsafeRead #-}
    basicUnsafeRead (MV_CellEntry v) i = coerce <$> VM.basicUnsafeRead v i

    {-# INLINE basicUnsafeWrite #-}
    basicUnsafeWrite (MV_CellEntry v) i x = VM.basicUnsafeWrite v i (coerce x)

    {-# INLINE basicClear #-}
    basicClear (MV_CellEntry v) = VM.basicClear v

    {-# INLINE basicSet #-}
    basicSet (MV_CellEntry v) x = VM.basicSet v (coerce x)

    {-# INLINE basicUnsafeCopy #-}
    basicUnsafeCopy (MV_CellEntry v1) (MV_CellEntry v2) = VM.basicUnsafeCopy v1 v2

    basicUnsafeMove (MV_CellEntry v1) (MV_CellEntry v2) = VM.basicUnsafeMove v1 v2

    {-# INLINE basicUnsafeGrow #-}
    basicUnsafeGrow (MV_CellEntry v) n = MV_CellEntry <$> VM.basicUnsafeGrow v n


instance VG.Vector VU.Vector CellEntry where

    {-# INLINE basicUnsafeFreeze #-}
    basicUnsafeFreeze (MV_CellEntry v) = V_CellEntry <$> VG.basicUnsafeFreeze v

    {-# INLINE basicUnsafeThaw #-}
    basicUnsafeThaw (V_CellEntry v) = MV_CellEntry <$> VG.basicUnsafeThaw v

    {-# INLINE basicLength #-}
    basicLength (V_CellEntry v) = VG.basicLength v

    {-# INLINE basicUnsafeSlice #-}
    basicUnsafeSlice i n (V_CellEntry v) = V_CellEntry $ VG.basicUnsafeSlice i n v

    {-# INLINE basicUnsafeIndexM #-}
    basicUnsafeIndexM (V_CellEntry v) i = coerce <$> VG.basicUnsafeIndexM v i

    basicUnsafeCopy (MV_CellEntry mv) (V_CellEntry v) = VG.basicUnsafeCopy mv v

    {-# INLINE elemseq #-}
    elemseq _ = seq


{-
renderBytes :: Int -> CellEntry -> Builder
renderBytes i (CellEntry w)
    | w >= 1024 = renderPad (i - 2) (w `div` 1024) <> "GB"
    | w <=  999 = renderPad (i - 2)  w <> "MB"
    | otherwise = renderPad (i - 2)  1 <> "GB"
-}


renderPad :: Int -> Word -> Builder
renderPad i w =
    let n = length $ show w
        s = replicate (i - n) ' '
    in  fromString s <> fromDec w

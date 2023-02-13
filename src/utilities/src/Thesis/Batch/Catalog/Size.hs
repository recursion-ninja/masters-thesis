{-# Language GeneralizedNewtypeDeriving #-}
{-# Language OverloadedStrings #-}
{-# Language Strict #-}
{-# Language TypeFamilies #-}

module Thesis.Batch.Catalog.Size
    ( Size ()
    ) where

import Control.Monad (when)
import Data.Coerce
import Data.Foldable (fold)
import Data.String (IsString(fromString))
import Data.Text.Builder.Linear (Builder, fromDec)
import Data.Vector.Generic qualified as VG
import Data.Vector.Generic.Mutable qualified as VM
import Data.Vector.Primitive qualified as VP
import Data.Vector.Unboxed (Unbox)
import Data.Vector.Unboxed qualified as VU
import Data.Word (Word8)
import Numeric.Natural
import Text.Read
import Thesis.Batch.Printer.Class


newtype Size
    = Size Word8


instance Bounded Size where

    minBound = Size 0

    maxBound = Size 254


newtype instance VU.MVector s Size = MV_Size (VP.MVector s Word8)


newtype instance VU.Vector    Size = V_Size  (VP.Vector    Word8)


deriving newtype instance Enum Size


deriving newtype instance Eq Size


deriving newtype instance Ord Size


instance RenderableCellEntry Size where

    renderCellEntry = renderPad 6


instance RenderableChoice Size where

    renderChoiceName = const "Param"

    renderChoiceNote = renderPad 6

    renderChoiceUnit = const " Nat "


instance Show Size where

    show (Size w) = show w


instance Read Size where

    {-# INLINABLE readPrec #-}
    readPrec =
        let (Size w)      = maxBound
            maximumNumber = fromIntegral w :: Natural
        in  do
            nat <- readPrec
            when (nat > maximumNumber)
                $ let note = ["Value '", show nat, "' is greater than maxBound '", show w, "'"]
                  in  fail $ fold note

            pure . Size $ fromIntegral nat

    readListPrec = readListPrecDefault


deriving newtype instance Unbox Size


instance VM.MVector VU.MVector Size where

    {-# INLINE basicLength #-}
    basicLength (MV_Size v) = VM.basicLength v

    {-# INLINE basicUnsafeSlice #-}
    basicUnsafeSlice i n (MV_Size v) = MV_Size $ VM.basicUnsafeSlice i n v

    {-# INLINE basicOverlaps #-}
    basicOverlaps (MV_Size v1) (MV_Size v2) = VM.basicOverlaps v1 v2

    {-# INLINE basicUnsafeNew #-}
    basicUnsafeNew n = MV_Size <$> VM.basicUnsafeNew n

    {-# INLINE basicInitialize #-}
    basicInitialize (MV_Size v) = VM.basicInitialize v

    {-# INLINE basicUnsafeReplicate #-}
    basicUnsafeReplicate n x = MV_Size <$> VM.basicUnsafeReplicate n (coerce x)

    {-# INLINE basicUnsafeRead #-}
    basicUnsafeRead (MV_Size v) i = coerce <$> VM.basicUnsafeRead v i

    {-# INLINE basicUnsafeWrite #-}
    basicUnsafeWrite (MV_Size v) i x = VM.basicUnsafeWrite v i (coerce x)

    {-# INLINE basicClear #-}
    basicClear (MV_Size v) = VM.basicClear v

    {-# INLINE basicSet #-}
    basicSet (MV_Size v) x = VM.basicSet v (coerce x)

    {-# INLINE basicUnsafeCopy #-}
    basicUnsafeCopy (MV_Size v1) (MV_Size v2) = VM.basicUnsafeCopy v1 v2

    basicUnsafeMove (MV_Size v1) (MV_Size v2) = VM.basicUnsafeMove v1 v2

    {-# INLINE basicUnsafeGrow #-}
    basicUnsafeGrow (MV_Size v) n = MV_Size <$> VM.basicUnsafeGrow v n


instance VG.Vector VU.Vector Size where

    {-# INLINE basicUnsafeFreeze #-}
    basicUnsafeFreeze (MV_Size v) = V_Size <$> VG.basicUnsafeFreeze v

    {-# INLINE basicUnsafeThaw #-}
    basicUnsafeThaw (V_Size v) = MV_Size <$> VG.basicUnsafeThaw v

    {-# INLINE basicLength #-}
    basicLength (V_Size v) = VG.basicLength v

    {-# INLINE basicUnsafeSlice #-}
    basicUnsafeSlice i n (V_Size v) = V_Size $ VG.basicUnsafeSlice i n v

    {-# INLINE basicUnsafeIndexM #-}
    basicUnsafeIndexM (V_Size v) i = coerce <$> VG.basicUnsafeIndexM v i

    basicUnsafeCopy (MV_Size mv) (V_Size v) = VG.basicUnsafeCopy mv v

    {-# INLINE elemseq #-}
    elemseq _ = seq


renderPad :: Int -> Size -> Builder
renderPad i (Size w) =
    let n = length $ show w
        p = replicate (i - n - 2) ' '
    in  fromString p <> fromDec w <> "  "

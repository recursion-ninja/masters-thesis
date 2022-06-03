{-# Language GeneralizedNewtypeDeriving #-}
{-# Language OverloadedStrings #-}
{-# Language Strict #-}
{-# Language TypeFamilies #-}

module Thesis.Batch.Catalog.Parameter
    ( Parameter ()
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


newtype Parameter
    = Parameter Word8


instance Bounded Parameter where

    minBound = Parameter 0

    maxBound = Parameter 254


newtype instance VU.MVector s Parameter = MV_Parameter (VP.MVector s Word8)


newtype instance VU.Vector    Parameter = V_Parameter  (VP.Vector    Word8)


deriving newtype instance Enum Parameter


deriving newtype instance Eq Parameter


deriving newtype instance Ord Parameter


instance RenderableCell Parameter where

    renderCell = renderPad 6


instance RenderableChoice Parameter where

    renderChoiceName = const "Param"

    renderChoiceNote = renderPad 6

    renderChoiceUnit = const " Nat "


instance Show Parameter where

    show (Parameter w) = show w


instance Read Parameter where

    {-# INLINABLE readPrec #-}
    readPrec =
        let (Parameter w) = maxBound
            maximumNumber = fromIntegral w :: Natural
        in  do
            nat <- readPrec
            when (nat > maximumNumber)
                $ let note = ["Value '", show nat, "' is greater than maxBound '", show w, "'"]
                  in  fail $ fold note

            pure . Parameter $ fromIntegral nat

    readListPrec = readListPrecDefault


deriving newtype instance Unbox Parameter


instance VM.MVector VU.MVector Parameter where

    {-# INLINE basicLength #-}
    basicLength (MV_Parameter v) = VM.basicLength v

    {-# INLINE basicUnsafeSlice #-}
    basicUnsafeSlice i n (MV_Parameter v) = MV_Parameter $ VM.basicUnsafeSlice i n v

    {-# INLINE basicOverlaps #-}
    basicOverlaps (MV_Parameter v1) (MV_Parameter v2) = VM.basicOverlaps v1 v2

    {-# INLINE basicUnsafeNew #-}
    basicUnsafeNew n = MV_Parameter <$> VM.basicUnsafeNew n

    {-# INLINE basicInitialize #-}
    basicInitialize (MV_Parameter v) = VM.basicInitialize v

    {-# INLINE basicUnsafeReplicate #-}
    basicUnsafeReplicate n x = MV_Parameter <$> VM.basicUnsafeReplicate n (coerce x)

    {-# INLINE basicUnsafeRead #-}
    basicUnsafeRead (MV_Parameter v) i = coerce <$> VM.basicUnsafeRead v i

    {-# INLINE basicUnsafeWrite #-}
    basicUnsafeWrite (MV_Parameter v) i x = VM.basicUnsafeWrite v i (coerce x)

    {-# INLINE basicClear #-}
    basicClear (MV_Parameter v) = VM.basicClear v

    {-# INLINE basicSet #-}
    basicSet (MV_Parameter v) x = VM.basicSet v (coerce x)

    {-# INLINE basicUnsafeCopy #-}
    basicUnsafeCopy (MV_Parameter v1) (MV_Parameter v2) = VM.basicUnsafeCopy v1 v2

    basicUnsafeMove (MV_Parameter v1) (MV_Parameter v2) = VM.basicUnsafeMove v1 v2

    {-# INLINE basicUnsafeGrow #-}
    basicUnsafeGrow (MV_Parameter v) n = MV_Parameter <$> VM.basicUnsafeGrow v n


instance VG.Vector VU.Vector Parameter where

    {-# INLINE basicUnsafeFreeze #-}
    basicUnsafeFreeze (MV_Parameter v) = V_Parameter <$> VG.basicUnsafeFreeze v

    {-# INLINE basicUnsafeThaw #-}
    basicUnsafeThaw (V_Parameter v) = MV_Parameter <$> VG.basicUnsafeThaw v

    {-# INLINE basicLength #-}
    basicLength (V_Parameter v) = VG.basicLength v

    {-# INLINE basicUnsafeSlice #-}
    basicUnsafeSlice i n (V_Parameter v) = V_Parameter $ VG.basicUnsafeSlice i n v

    {-# INLINE basicUnsafeIndexM #-}
    basicUnsafeIndexM (V_Parameter v) i = coerce <$> VG.basicUnsafeIndexM v i

    basicUnsafeCopy (MV_Parameter mv) (V_Parameter v) = VG.basicUnsafeCopy mv v

    {-# INLINE elemseq #-}
    elemseq _ = seq


renderPad :: Int -> Parameter -> Builder
renderPad i (Parameter w) =
    let n = length $ show w
        p = replicate (i - n - 2) ' '
    in  fromString p <> fromDec w <> "  "

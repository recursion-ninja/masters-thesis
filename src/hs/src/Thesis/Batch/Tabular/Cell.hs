{-# Language GeneralizedNewtypeDeriving #-}
{-# Language OverloadedStrings #-}
{-# Language Strict #-}
{-# Language TypeFamilies #-}

module Thesis.Batch.Tabular.Cell
    ( Cell ()
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


newtype Cell
    = Cell Word


newtype instance VU.MVector s Cell = MV_Cell (VP.MVector s Word)


newtype instance VU.Vector    Cell = V_Cell  (VP.Vector    Word)


instance Bounded Cell where

    minBound = Cell 0

    maxBound = Cell 983040


deriving newtype instance Enum Cell


deriving newtype instance Eq Cell


deriving newtype instance Ord Cell


instance RenderableCell Cell where

    renderCell (Cell w) = renderPad 6 w


instance RenderableChoice Cell where

    renderChoiceName = const " Cell "

    renderChoiceNote = renderCell

    renderChoiceUnit = const " Byte "


instance Show Cell where

    show (Cell w) = show w


instance Read Cell where

    {-# INLINABLE readPrec #-}
    readPrec =
        let (Cell v) = maxBound
            maxValue = fromIntegral v :: Natural
            vWord    = do
                nat <- readPrec
                when (nat > maxValue) . fail $ fold
                    ["Value '", show nat, "' is greater than maxBound '", show v, "'"]
                pure . Cell $ fromIntegral nat

            vBool = do
                c <- get
                if c `elem` (fromList "tTyY⊤" :: Set Char)
                    then pure $ Cell 1
                    else if c `elem` (fromList "fFnN⊥" :: Set Char)
                        then pure $ Cell 0
                        else fail $ fold ["Unexpected value '", show c, "' found in table cell"]
        in  vBool <|> vWord

    readListPrec = readListPrecDefault


deriving newtype instance Unbox Cell


instance VM.MVector VU.MVector Cell where

    {-# INLINE basicLength #-}
    basicLength (MV_Cell v) = VM.basicLength v

    {-# INLINE basicUnsafeSlice #-}
    basicUnsafeSlice i n (MV_Cell v) = MV_Cell $ VM.basicUnsafeSlice i n v

    {-# INLINE basicOverlaps #-}
    basicOverlaps (MV_Cell v1) (MV_Cell v2) = VM.basicOverlaps v1 v2

    {-# INLINE basicUnsafeNew #-}
    basicUnsafeNew n = MV_Cell <$> VM.basicUnsafeNew n

    {-# INLINE basicInitialize #-}
    basicInitialize (MV_Cell v) = VM.basicInitialize v

    {-# INLINE basicUnsafeReplicate #-}
    basicUnsafeReplicate n x = MV_Cell <$> VM.basicUnsafeReplicate n (coerce x)

    {-# INLINE basicUnsafeRead #-}
    basicUnsafeRead (MV_Cell v) i = coerce <$> VM.basicUnsafeRead v i

    {-# INLINE basicUnsafeWrite #-}
    basicUnsafeWrite (MV_Cell v) i x = VM.basicUnsafeWrite v i (coerce x)

    {-# INLINE basicClear #-}
    basicClear (MV_Cell v) = VM.basicClear v

    {-# INLINE basicSet #-}
    basicSet (MV_Cell v) x = VM.basicSet v (coerce x)

    {-# INLINE basicUnsafeCopy #-}
    basicUnsafeCopy (MV_Cell v1) (MV_Cell v2) = VM.basicUnsafeCopy v1 v2

    basicUnsafeMove (MV_Cell v1) (MV_Cell v2) = VM.basicUnsafeMove v1 v2

    {-# INLINE basicUnsafeGrow #-}
    basicUnsafeGrow (MV_Cell v) n = MV_Cell <$> VM.basicUnsafeGrow v n


instance VG.Vector VU.Vector Cell where

    {-# INLINE basicUnsafeFreeze #-}
    basicUnsafeFreeze (MV_Cell v) = V_Cell <$> VG.basicUnsafeFreeze v

    {-# INLINE basicUnsafeThaw #-}
    basicUnsafeThaw (V_Cell v) = MV_Cell <$> VG.basicUnsafeThaw v

    {-# INLINE basicLength #-}
    basicLength (V_Cell v) = VG.basicLength v

    {-# INLINE basicUnsafeSlice #-}
    basicUnsafeSlice i n (V_Cell v) = V_Cell $ VG.basicUnsafeSlice i n v

    {-# INLINE basicUnsafeIndexM #-}
    basicUnsafeIndexM (V_Cell v) i = coerce <$> VG.basicUnsafeIndexM v i

    basicUnsafeCopy (MV_Cell mv) (V_Cell v) = VG.basicUnsafeCopy mv v

    {-# INLINE elemseq #-}
    elemseq _ = seq


{-
renderBytes :: Int -> Cell -> Builder
renderBytes i (Cell w)
    | w >= 1024 = renderPad (i - 2) (w `div` 1024) <> "GB"
    | w <=  999 = renderPad (i - 2)  w <> "MB"
    | otherwise = renderPad (i - 2)  1 <> "GB"
-}


renderPad :: Int -> Word -> Builder
renderPad i w =
    let n = length $ show w
        s = replicate (i - n) ' '
    in  fromString s <> fromDec w

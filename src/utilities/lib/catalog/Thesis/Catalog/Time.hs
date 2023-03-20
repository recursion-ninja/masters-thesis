{-# Language GeneralizedNewtypeDeriving #-}
{-# Language OverloadedStrings #-}
{-# Language Strict #-}
{-# Language TypeFamilies #-}

module Thesis.Catalog.Time
    ( Time ()
    ) where

import Control.Monad (when)
import Data.Coerce
import Data.Foldable (fold)
import Data.Vector.Generic qualified as VG
import Data.Vector.Generic.Mutable qualified as VM
import Data.Vector.Primitive qualified as VP
import Data.Vector.Unboxed (Unbox)
import Data.Vector.Unboxed qualified as VU
import Data.Word (Word8)
import Numeric.Natural
import Text.Read


newtype Time
    = Time Word8


instance Bounded Time where

    minBound = Time 0

    maxBound = Time 254


newtype instance VU.MVector s Time = MV_Time (VP.MVector s Word8)


newtype instance VU.Vector    Time = V_Time  (VP.Vector    Word8)


deriving newtype instance Enum Time


deriving newtype instance Eq Time


deriving newtype instance Ord Time


instance Show Time where

    show (Time w) = show w


instance Read Time where

    {-# INLINABLE readPrec #-}
    readPrec =
        let (Time w)      = maxBound
            maximumNumber = fromIntegral w :: Natural
        in  do
            nat <- readPrec
            when (nat > maximumNumber)
                $ let note = ["Value '", show nat, "' is greater than maxBound '", show w, "'"]
                  in  fail $ fold note

            pure . Time $ fromIntegral nat

    readListPrec = readListPrecDefault


deriving newtype instance Unbox Time


instance VM.MVector VU.MVector Time where

    {-# INLINE basicLength #-}
    basicLength (MV_Time v) = VM.basicLength v

    {-# INLINE basicUnsafeSlice #-}
    basicUnsafeSlice i n (MV_Time v) = MV_Time $ VM.basicUnsafeSlice i n v

    {-# INLINE basicOverlaps #-}
    basicOverlaps (MV_Time v1) (MV_Time v2) = VM.basicOverlaps v1 v2

    {-# INLINE basicUnsafeNew #-}
    basicUnsafeNew n = MV_Time <$> VM.basicUnsafeNew n

    {-# INLINE basicInitialize #-}
    basicInitialize (MV_Time v) = VM.basicInitialize v

    {-# INLINE basicUnsafeReplicate #-}
    basicUnsafeReplicate n x = MV_Time <$> VM.basicUnsafeReplicate n (coerce x)

    {-# INLINE basicUnsafeRead #-}
    basicUnsafeRead (MV_Time v) i = coerce <$> VM.basicUnsafeRead v i

    {-# INLINE basicUnsafeWrite #-}
    basicUnsafeWrite (MV_Time v) i x = VM.basicUnsafeWrite v i (coerce x)

    {-# INLINE basicClear #-}
    basicClear (MV_Time v) = VM.basicClear v

    {-# INLINE basicSet #-}
    basicSet (MV_Time v) x = VM.basicSet v (coerce x)

    {-# INLINE basicUnsafeCopy #-}
    basicUnsafeCopy (MV_Time v1) (MV_Time v2) = VM.basicUnsafeCopy v1 v2

    basicUnsafeMove (MV_Time v1) (MV_Time v2) = VM.basicUnsafeMove v1 v2

    {-# INLINE basicUnsafeGrow #-}
    basicUnsafeGrow (MV_Time v) n = MV_Time <$> VM.basicUnsafeGrow v n


instance VG.Vector VU.Vector Time where

    {-# INLINE basicUnsafeFreeze #-}
    basicUnsafeFreeze (MV_Time v) = V_Time <$> VG.basicUnsafeFreeze v

    {-# INLINE basicUnsafeThaw #-}
    basicUnsafeThaw (V_Time v) = MV_Time <$> VG.basicUnsafeThaw v

    {-# INLINE basicLength #-}
    basicLength (V_Time v) = VG.basicLength v

    {-# INLINE basicUnsafeSlice #-}
    basicUnsafeSlice i n (V_Time v) = V_Time $ VG.basicUnsafeSlice i n v

    {-# INLINE basicUnsafeIndexM #-}
    basicUnsafeIndexM (V_Time v) i = coerce <$> VG.basicUnsafeIndexM v i

    basicUnsafeCopy (MV_Time mv) (V_Time v) = VG.basicUnsafeCopy mv v

    {-# INLINE elemseq #-}
    elemseq _ = seq

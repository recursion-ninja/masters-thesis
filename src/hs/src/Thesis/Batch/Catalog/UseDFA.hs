{-# Language DerivingStrategies #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language OverloadedStrings #-}
{-# Language Strict #-}
{-# Language TypeFamilies #-}

module Thesis.Batch.Catalog.UseDFA
    ( UseDFA ()
    , enumUseDFA
    , useDFA
    ) where

import Data.Coerce
import Data.Text.Builder.Linear
import Data.Vector.Generic qualified as VG
import Data.Vector.Generic.Mutable qualified as VM
import Data.Vector.Primitive qualified as VP
import Data.Vector.Unboxed (Unbox)
import Data.Vector.Unboxed qualified as VU
import Data.Word (Word8)
import Thesis.Batch.Printer.Class


newtype UseDFA
    = UseDFA Word8


newtype instance VU.MVector s UseDFA = MV_UseDFA (VP.MVector s Word8)


newtype instance VU.Vector    UseDFA = V_UseDFA  (VP.Vector    Word8)


deriving newtype instance Eq UseDFA


deriving newtype instance Ord UseDFA


instance RenderableCell UseDFA where

    renderCell bv
        | useDFA bv = "   ⊤  "
        | otherwise = "   ⊥  "


instance RenderableChoice UseDFA where

    renderChoiceName = const $ fromText "DFAMIN"

    renderChoiceNote bv
        | useDFA bv = "  YES "
        | otherwise = "  NAY "

    renderChoiceUnit = const $ fromText "Binary"


instance Show UseDFA where

    show bv
        | useDFA bv = "Yes"
        | otherwise = "No"


deriving newtype instance Unbox UseDFA


instance VM.MVector VU.MVector UseDFA where

    {-# INLINE basicLength #-}
    basicLength (MV_UseDFA v) = VM.basicLength v

    {-# INLINE basicUnsafeSlice #-}
    basicUnsafeSlice i n (MV_UseDFA v) = MV_UseDFA $ VM.basicUnsafeSlice i n v

    {-# INLINE basicOverlaps #-}
    basicOverlaps (MV_UseDFA v1) (MV_UseDFA v2) = VM.basicOverlaps v1 v2

    {-# INLINE basicUnsafeNew #-}
    basicUnsafeNew n = MV_UseDFA <$> VM.basicUnsafeNew n

    {-# INLINE basicInitialize #-}
    basicInitialize (MV_UseDFA v) = VM.basicInitialize v

    {-# INLINE basicUnsafeReplicate #-}
    basicUnsafeReplicate n x = MV_UseDFA <$> VM.basicUnsafeReplicate n (coerce x)

    {-# INLINE basicUnsafeRead #-}
    basicUnsafeRead (MV_UseDFA v) i = coerce <$> VM.basicUnsafeRead v i

    {-# INLINE basicUnsafeWrite #-}
    basicUnsafeWrite (MV_UseDFA v) i x = VM.basicUnsafeWrite v i (coerce x)

    {-# INLINE basicClear #-}
    basicClear (MV_UseDFA v) = VM.basicClear v

    {-# INLINE basicSet #-}
    basicSet (MV_UseDFA v) x = VM.basicSet v (coerce x)

    {-# INLINE basicUnsafeCopy #-}
    basicUnsafeCopy (MV_UseDFA v1) (MV_UseDFA v2) = VM.basicUnsafeCopy v1 v2

    basicUnsafeMove (MV_UseDFA v1) (MV_UseDFA v2) = VM.basicUnsafeMove v1 v2

    {-# INLINE basicUnsafeGrow #-}
    basicUnsafeGrow (MV_UseDFA v) n = MV_UseDFA <$> VM.basicUnsafeGrow v n


instance VG.Vector VU.Vector UseDFA where

    {-# INLINE basicUnsafeFreeze #-}
    basicUnsafeFreeze (MV_UseDFA v) = V_UseDFA <$> VG.basicUnsafeFreeze v

    {-# INLINE basicUnsafeThaw #-}
    basicUnsafeThaw (V_UseDFA v) = MV_UseDFA <$> VG.basicUnsafeThaw v

    {-# INLINE basicLength #-}
    basicLength (V_UseDFA v) = VG.basicLength v

    {-# INLINE basicUnsafeSlice #-}
    basicUnsafeSlice i n (V_UseDFA v) = V_UseDFA $ VG.basicUnsafeSlice i n v

    {-# INLINE basicUnsafeIndexM #-}
    basicUnsafeIndexM (V_UseDFA v) i = coerce <$> VG.basicUnsafeIndexM v i

    basicUnsafeCopy (MV_UseDFA mv) (V_UseDFA v) = VG.basicUnsafeCopy mv v

    {-# INLINE elemseq #-}
    elemseq _ = seq


enumUseDFA :: (Enum e, Eq e) => e -> UseDFA
enumUseDFA =
    let zero = toEnum 0
        isZero v
            | zero == v = minBound
            | otherwise = maxBound
    in  UseDFA . isZero


useDFA :: UseDFA -> Bool
useDFA (UseDFA 0) = False
useDFA _          = True

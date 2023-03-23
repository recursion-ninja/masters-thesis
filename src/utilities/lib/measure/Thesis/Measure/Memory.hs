{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE UnboxedSums #-}

module Thesis.Measure.Memory
  ( -- * Data-types
    Memory()
  , BinaryMagnitude(..)
    -- * Construction
  , asMagnitude
  -- * Rendering
  , renderMagnitude
  ) where


import Control.DeepSeq
import Data.Foldable (fold)
import Data.List (unfoldr)
import GHC.Exts (IsString(fromString))
import Numeric.Natural


-- | Information measurement with Byte resolution.
newtype Memory = Memory Natural
    deriving (Eq, Ord)


data  BinaryMagnitude
    = B
    | KiB
    | MiB
    | GiB
    | TiB
    | PiB
    | EiB
    | ZiB
    | YiB
    deriving (Bounded, Enum, Eq, Ord, Show)


instance NFData BinaryMagnitude where

    rnf (!_) = ()


instance NFData Memory where

    rnf (Memory !_) = ()


instance Show Memory where

    show mem@(Memory x) =
        let mag = inferMagnitude x
        in  renderMagnitude mag mem


asMagnitude :: Real n => n -> BinaryMagnitude -> Memory
asMagnitude input mag =
    let num = toRational input
        res = toRational $ magnitudeResolution mag
    in  Memory . round $ num * res


renderMagnitude :: IsString s => BinaryMagnitude -> Memory -> s
renderMagnitude mag (Memory x) =
    let pad :: Show a => Int -> a -> String
        pad n s =
             let str = show s
                 len = length str
             in str <> replicate (n - len) '0'

        res :: Natural
        res = magnitudeResolution mag

        (q,r) = x `divMod` res

    in  fromString $ fold [show q, ".", pad 3 r, " ", show mag ]


-- Internal


binaryMagitude :: Natural
binaryMagitude = 1024


inferMagnitude :: Natural -> BinaryMagnitude
inferMagnitude =
    let f 0 = Nothing
        f x = Just (x, x `div` binaryMagitude)
    in  fst . last . zip [minBound .. maxBound] . unfoldr f


magnitudeResolution :: BinaryMagnitude -> Natural
magnitudeResolution mag =
    let applyBasis :: Functor f => f a -> f Natural
        applyBasis = (binaryMagitude <$)
    in  product . applyBasis $ takeWhile (< mag) [minBound .. maxBound]

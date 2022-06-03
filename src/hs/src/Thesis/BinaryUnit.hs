{-# Language Safe #-}

module Thesis.BinaryUnit
    ( Bin0
    , Bin1
    , Bin2
    , Bin3
    , Bin4
    , Bin5
    , Bin6
    , Bin7
    , Bin8
    , Byte
    , EiB
    , GiB
    , KiB
    , MiB
    , PiB
    , TiB
    , YiB
    , ZiB
    ) where

import Data.Fixed


data  Bin0


data  Bin1


data  Bin2


data  Bin3


data  Bin4


data  Bin5


data  Bin6


data  Bin7


data  Bin8


type Byte = Fixed Bin0


type KiB = Fixed Bin1


type MiB = Fixed Bin2


type GiB = Fixed Bin3


type TiB = Fixed Bin4


type PiB = Fixed Bin5


type EiB = Fixed Bin6


type ZiB = Fixed Bin7


type YiB = Fixed Bin8


instance HasResolution Bin0 where

    resolution = const 1


instance HasResolution Bin1 where

    resolution = const binaryMagitude


instance HasResolution Bin2 where

    resolution = const $ binaryMagitude ^ 2


instance HasResolution Bin3 where

    resolution = const $ binaryMagitude ^ 3


instance HasResolution Bin4 where

    resolution = const $ binaryMagitude ^ 4


instance HasResolution Bin5 where

    resolution = const $ binaryMagitude ^ 5


instance HasResolution Bin6 where

    resolution = const $ binaryMagitude ^ 6


instance HasResolution Bin7 where

    resolution = const $ binaryMagitude ^ 7


instance HasResolution Bin8 where

    resolution = const $ binaryMagitude ^ 8


binaryMagitude :: Integer
binaryMagitude = 1024

{-# Language DerivingStrategies #-}
{-# Language ExistentialQuantification #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}

module Thesis.ExtractedRow
    ( ExtractedRow (..)
    ) where

import Data.ByteString (ByteString)
import Data.ByteString.Char8 (unwords)
import Data.Csv (DefaultOrdered(..), ToField(..), ToNamedRecord(..), namedRecord, (.=))
import Data.Fixed (Fixed(MkFixed), Pico, resolution)
import Data.Foldable
import Data.List (sort)
import Data.Ratio
import Data.Scientific (FPFormat(Fixed), Scientific, formatScientific)
import Data.Time.Clock (DiffTime, diffTimeToPicoseconds, nominalDay, secondsToDiffTime)
import Data.Time.Format (defaultTimeLocale, formatTime)
import Data.Time.LocalTime (timeToTimeOfDay)
import GHC.Exts (IsList(fromList))
import Prelude hiding (putStr, readFile, unwords)
import Thesis.BinaryUnit
import Unsafe.Coerce (unsafeCoerce)


data  ExtractedRow
    = ExtractedRow
    { rowVersion     :: Word
    , rowProperty    :: ByteString
    , rowSecurityT   :: Word
    , rowSecurityN   :: Word
    , rowRuntime     :: DiffTime
    , rowMemory      :: MiB
    , rowVectorLen   :: Word -- Bytes
    , rowStates      :: Word
    , rowTransitions :: Word
    , rowDirectives  :: [ByteString]
    }


deriving stock instance Show ExtractedRow


data Fieldable = forall a . ToField a
    => FieldValueOf a


instance DefaultOrdered ExtractedRow where

    headerOrder = const $ fromList
        [ "Version"
        , "LTL"
        , "T"
        , "N"
        , "Runtime (seconds)"
        , "Runtime (timestamp)"
        , "Mebibytes"
        , "Memory (Human)"
        , "State Vector (bytes)"
        , "States"
        , "Transitions"
        , "Compilation Directives"
        ]


instance ToNamedRecord ExtractedRow where

    toNamedRecord row@(ExtractedRow {..}) =
        let encodeFieldValue :: ByteString -> Fieldable -> (ByteString, ByteString)
            encodeFieldValue key (FieldValueOf val) = key .= val

            fieldKeys = toList $ headerOrder row

            diffToSecs :: DiffTime -> Integer
            diffToSecs = (`div` resolution (1 :: Pico)) . diffTimeToPicoseconds

            rowRuntime' :: Integer
            rowRuntime' = diffToSecs rowRuntime

            rowWallClock :: String
            rowWallClock =
                let runInSeconds = diffToSecs rowRuntime
                    dayInSeconds = diffToSecs $ unsafeCoerce nominalDay
                    todInSeconds = timeToTimeOfDay . secondsToDiffTime
                    printSeconds = formatTime defaultTimeLocale "%Hh %Mm %Ss" . todInSeconds
                    (days, time) = runInSeconds `quotRem` dayInSeconds
                in  fold [show days, "d ", printSeconds time]

            scientificBytes = formatScientific Fixed (Just 3)

            rowMebibytes :: String
            rowMebibytes =
                let (MkFixed bytes) = rowMemory
                    mebi :: Scientific
                    mebi = fromRational $ bytes % resolution (1 :: MiB)
                in  scientificBytes mebi

            rowMemory' :: String
            rowMemory' =
                let (MkFixed bytes) = rowMemory
                    oneMebi = resolution (1 :: MiB)
                    oneGibi = resolution (1 :: GiB)
                    (scaling, abrev)
                        | bytes < oneGibi = (oneMebi, "MiB")
                        | otherwise       = (oneGibi, "Gib")
                    humanForm = fromRational $ bytes % scaling
                in  scientificBytes humanForm <> " " <> abrev

            rowDirectives' :: ByteString
            rowDirectives' = unwords $ sort rowDirectives
            
        in  namedRecord $ zipWith
            encodeFieldValue
            fieldKeys
            [ FieldValueOf rowVersion
            , FieldValueOf rowProperty
            , FieldValueOf rowSecurityT
            , FieldValueOf rowSecurityN
            , FieldValueOf rowRuntime'
            , FieldValueOf rowWallClock
            , FieldValueOf rowMebibytes
            , FieldValueOf rowMemory'
            , FieldValueOf rowVectorLen
            , FieldValueOf rowStates
            , FieldValueOf rowTransitions
            , FieldValueOf rowDirectives'
            ]


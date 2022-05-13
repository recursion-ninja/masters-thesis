{-# Language DerivingStrategies #-}
{-# Language ExistentialQuantification #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}

module ExtractedRow
    ( ExtractedRow (..)
    ) where

import BinaryUnit
import Data.ByteString (ByteString, intercalate)
import Data.Csv (DefaultOrdered(..), ToField(..), ToNamedRecord(..))
import Data.Csv (namedRecord, (.=))
import Data.Fixed (Fixed(MkFixed), Pico, resolution)
import Data.Foldable
import Data.List (sort)
import Data.Ratio
import Data.Scientific (FPFormat(Fixed), Scientific, formatScientific)
import Data.Time.Clock (DiffTime, diffTimeToPicoseconds)
import GHC.Exts (IsList(fromList))
import Prelude hiding (putStr, readFile)


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
        , "Memory (GiBs)"
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

            rowRuntime' :: Integer
            rowRuntime' = (`div` resolution (1 :: Pico)) $ diffTimeToPicoseconds rowRuntime

            rowMemory' :: String
            rowMemory' =
                let (MkFixed bytes) = rowMemory
                    gibi :: Scientific
                    gibi = fromRational $ bytes % resolution (1 :: GiB)
                in  formatScientific Fixed (Just 3) gibi

            rowDirectives' :: ByteString
            rowDirectives' = intercalate " " $ sort rowDirectives
        in  namedRecord $ zipWith
            encodeFieldValue
            fieldKeys
            [ FieldValueOf rowVersion
            , FieldValueOf rowProperty
            , FieldValueOf rowSecurityT
            , FieldValueOf rowSecurityN
            , FieldValueOf rowRuntime'
            , FieldValueOf rowMemory'
            , FieldValueOf rowVectorLen
            , FieldValueOf rowStates
            , FieldValueOf rowTransitions
            , FieldValueOf rowDirectives'
            ]


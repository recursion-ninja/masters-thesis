{-# Language DeriveAnyClass #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language OverloadedStrings #-}
{-# Language Strict #-}

module Thesis.Measure.Benchmark.Set
  ( -- * Data-types
    BenchmarkSeriesSet(..)
  , BenchmarkSeriesKey(..)
  , BenchmarkFileContent(..)
  , BenchmarkSeriesTable(..)
  , BenchmarkMetadata(..)
  , BenchmarkSeriesRow(..)
  , BenchmarkNamedRecord()
    -- ** Constructor
  , colateBenchmarkSeries
    -- ** Accessor
  , extractBenchmarkIndex
  , extractBenchmarkMetadata
  , extractBenchmarkRow
  , extractRowsForCSV
  ) where


import Control.DeepSeq
import Data.Csv (DefaultOrdered(..), Field, NamedRecord, ToField(..), ToNamedRecord(..), namedRecord, (.=))
import Data.Functor (($>))
--import Data.Foldable (toList)
import Data.IntMap.Strict (IntMap, insert, singleton)
import Data.List (intercalate, sort, transpose, unfoldr)
import Data.Map.Strict (Map, alter, toAscList, foldrWithKey')
--import Data.Maybe (fromMaybe, maybe)
import Data.Ratio
import Data.Semigroup (Arg(..), Max(..))
import Data.Text (Text, unpack)
import Data.Text qualified as T
import GHC.Exts (IsList(..), IsString(fromString))
import GHC.Generics (Generic)
--import Numeric.Natural
import Parser.SPIN (BackMatter(..), SpinMemory(..), SpinModel(..), SpinTiming(..))
import Parser.BenchScript

import Thesis.Catalog.LTL
import Thesis.Catalog.Membership
import Thesis.Catalog.Protocol
import Thesis.Measure.Benchmark.File(BenchmarkFileContent(..))


{- |
Nicely colated output type for consumption / pretty-printing.
-}
newtype BenchmarkSeriesSet = BenchmarkSeriesSet (Map BenchmarkSeriesKey BenchmarkSeriesMeasurement)


data  BenchmarkSeriesKey
    = BenchmarkSeriesKey
    { benchSeriesVersion  :: Protocol
    , benchSeriesProperty :: LTL
    , benchSeriesMembers  :: {-# UNPACK #-} Membership
    }


newtype BenchmarkSeriesMeasurement = BenchmarkSeriesMeasurement (Arg BenchmarkMetadata BenchmarkSeriesTable)


data  BenchmarkMetadata
    = BenchmarkMetadata
    { benchSeriesDirectivesConstant   :: BenchDirectiveSet
    , benchSeriesDirectivesExperiment :: BenchDirectiveSet
    , benchSeriesRuntimeFlags         :: BenchRuntimeFlags
    }


newtype BenchmarkSeriesTable = BenchmarkSeriesTable (IntMap BenchmarkSeriesRow)


data  BenchmarkSeriesRow
    = BenchmarkSeriesRow
    { benchChosenFlags   :: BenchDirectiveSet
    , benchMaybeSubModel :: Maybe BenchmarkSeriesSubModel
    }


data  BenchmarkSeriesSubModel
    = BenchmarkSeriesSubModel
    { benchSeriesModel :: SpinModel
    , benchSeriesSpace :: SpinMemory
    , benchSeriesTime  :: SpinTiming
    }


newtype BenchmarkNamedRecord = BenchmarkNamedRecord NamedRecord deriving (Show)


instance DefaultOrdered BenchmarkNamedRecord where

    headerOrder = const $ fromList 
        [ "Version"
        , "LTL"    
        , "N"      
        , "C"      
        , "E"      
        , "Flags"
        , "Directives"
        , "Errors"
        , "Runtime (s)"
        , "Memory (MiB)"
        , "Allocation (MiB)"
        , "Hashtable (MiB)"
        , "State-Vector (B)"
        , "Search Depth"
        , "States (stored)"
        , "States (matched)"
        , "Transitions"
        ]


instance ToNamedRecord BenchmarkNamedRecord where

    toNamedRecord (BenchmarkNamedRecord x) = x


deriving stock    instance Eq BenchmarkMetadata


deriving stock    instance Eq BenchmarkSeriesKey


deriving newtype  instance Eq BenchmarkSeriesMeasurement


deriving stock    instance Generic BenchmarkSeriesKey


deriving anyclass instance NFData BenchmarkSeriesKey


deriving stock    instance Ord BenchmarkMetadata


deriving newtype  instance Ord BenchmarkSeriesMeasurement


deriving stock    instance Ord BenchmarkSeriesKey


deriving stock    instance Show BenchmarkSeriesRow


deriving stock    instance Show BenchmarkSeriesSubModel


instance Show BenchmarkSeriesSet where

    show (BenchmarkSeriesSet mapping) =
        let keyValPairs :: [(BenchmarkSeriesKey, BenchmarkSeriesMeasurement)]
            keyValPairs = toAscList mapping

            showEntry :: (BenchmarkSeriesKey, BenchmarkSeriesMeasurement) -> String
            showEntry (k, v) = unlines [ show k, "", show v ]

        in  foldMap showEntry keyValPairs


instance Show BenchmarkSeriesKey where

    show (BenchmarkSeriesKey ver ltl size) =
        let comma :: Show a => a -> String
            comma = (<> ",") . show
        in  unwords
            [ "("
            , comma ver
            , comma ltl
            , "N = " <> show size
            , ")"
            ]


instance Show BenchmarkSeriesMeasurement where

    show (BenchmarkSeriesMeasurement (Arg meta table)) = unlines
        [ show meta
        , ""
        , show table
        ]


instance Show BenchmarkMetadata where

    show (BenchmarkMetadata c e f) =
        let getDirectives (BenchDirectiveSet ds) = sort $ toList ds
            getRunFlags   (BenchRuntimeFlags fs) = sort $ toList fs

            headers :: [Text]
            headers = [ "$\\mathcal{A}$", "$\\mathcal{C}$", "$\\mathcal{E}$", "$\\mathcal{F}$" ]

            columns :: [[Text]]
            columns =
                [ [ "-a" ]
                , getDirectives c
                , getDirectives e
                , getRunFlags   f
                ]
        in  T.unpack $ renderMarkdownFromColumns headers columns


instance Show BenchmarkSeriesTable where

    show = T.unpack . renderBenchmarkSeriesTable


extractRowsForCSV :: BenchmarkSeriesSet -> [BenchmarkNamedRecord]
extractRowsForCSV (BenchmarkSeriesSet mapping) =
    let makeNamedRecords :: BenchmarkSeriesKey -> BenchmarkSeriesMeasurement -> [BenchmarkNamedRecord] -> [BenchmarkNamedRecord]
        makeNamedRecords key val =
            let BenchmarkSeriesMeasurement (Arg meta (BenchmarkSeriesTable table)) = val

                getListing :: (IsList f, Item f ~ Text) => (BenchmarkMetadata -> f) -> Field
                getListing f = toCommaList $ f meta
                
                getPairing :: ToField b => [b] -> [(Field, Field)]
                getPairing = zipWith (.=)
                    [ "Directives"
                    , "Errors"
                    , "Runtime (s)"
                    , "Memory (MiB)"
                    , "Allocation (MiB)"
                    , "Hashtable (MiB)"
                    , "State-Vector (B)"
                    , "Search Depth"
                    , "States (stored)"
                    , "States (matched)"
                    , "Transitions"
                    ]

                verNum :: Enum e => e -> Int
                verNum = succ . fromEnum
                
                metaFields :: [(Field, Field)]
                metaFields =
                    [ "Version" .= verNum   (benchSeriesVersion  key)
                    , "LTL"     .= show     (benchSeriesProperty key)
                    , "N"       .= fromEnum (benchSeriesMembers  key)
                    , "C"       .= getListing benchSeriesDirectivesConstant
                    , "E"       .= getListing benchSeriesDirectivesExperiment
                    , "Flags"   .= getListing benchSeriesRuntimeFlags
                    ]


                makeRecord :: [Field] -> BenchmarkNamedRecord
                makeRecord = BenchmarkNamedRecord . namedRecord . (metaFields <>) . getPairing
                
                rowsFields = rowObservation . snd <$> toList table
                newRecords = makeRecord <$> rowsFields
            in  (newRecords <>)
    in  foldrWithKey' makeNamedRecords mempty mapping


toCommaList :: (IsList f, Item f ~ Text, IsString s) => f -> s
toCommaList = fromString . intercalate ", " . fmap unpack . toList


{-
Rendering functions
-}


rowObservation :: IsString s => BenchmarkSeriesRow -> [s]
rowObservation (BenchmarkSeriesRow flags maybeModel) =
    let getFlags :: IsString s => BenchDirectiveSet -> s
        getFlags (BenchDirectiveSet xs) = fromString . unwords $ unpack <$> toList xs

        absent =
            [ "SEGFAULT"
            , ""
            , ""
            , ""
            , ""
            , ""
            , ""
            , ""
            , ""
            , ""
            ]

        present :: IsString a => BenchmarkSeriesSubModel -> [a]
        present (BenchmarkSeriesSubModel model space time) =
            let nat :: (IsString s, Show a) => (SpinModel -> a) -> s
                nat f = fromString . show $ f model

                rat :: IsString s => Rational -> s
                rat r =
                    let (d, n) = abs num `quotRem` den
                        num = numerator r
                        den = denominator r

                        go 0 = shows 0 (go 0)
                        go x = let (y, next) = (10 * x) `quotRem` den
                               in  shows y (go next)
                    in  fromString $ shows d ("." ++ take 3 (go n))

                memTotal = memTotalUsed space
                memTable = memHashTable space
            in  [ nat searchErrors
                , rat $ timeElapsed time
                , rat   memTotal
                , rat $ memTotal - memTable
                , rat   memTable
                , nat stateVector
                , nat searchDepth
                , nat statesStored
                , nat statesMatched
                , nat transitions
                ]

    in  [ getFlags flags ] <> maybe absent present maybeModel


renderBenchmarkSeriesTable :: BenchmarkSeriesTable -> Text
renderBenchmarkSeriesTable (BenchmarkSeriesTable im) =
    let columns = transpose $ rowObservation . snd <$> toList im
        headers =
            [ "Directives"
            , "Errors"
            , "Runtime (s)"
            , "Memory (MiB)"
            , "Allocation (MiB)"
            , "Hashtable (MiB)"
            , "State-Vector (B)"
            , "Search Depth"
            , "States (stored)"
            , "States (matched)"
            , "Transitions"
            ]
    in  renderMarkdownFromColumns headers columns


renderMarkdownFromColumns
  :: [Text]   -- ^ Header
  -> [[Text]] -- ^ Columns
  -> Text
renderMarkdownFromColumns headers columns =
    let maxColumnHeight :: Word
        maxColumnHeight = maximumUsing (toEnum . length) columns

        addColumnHeight :: [Text] -> [Text]
        addColumnHeight col =
            let len = length col
            in  col <> replicate (fromEnum maxColumnHeight - len) ""

        regimentColumn :: [Text] -> [Text]
        regimentColumn = addColumnHeight . fmap asCode

        regColumns :: [[Text]]
        regColumns = regimentColumn <$> columns

        maxColumnWidth :: [Word]
        maxColumnWidth = zipWith (\h -> max (txtLen h) . maximumWidth) headers regColumns

        padColumnWidth :: Char -> Word -> Text -> Text
        padColumnWidth c dim txt =
            let len = txtLen txt
                pad = fromString [c]
            in  pad <> T.replicate (fromEnum dim - len) pad <> txt <> pad

        genRow :: Word -> Maybe ([Text], Word)
        genRow i
            | i == maxColumnHeight = Nothing
            | otherwise            = Just ( (!! fromEnum i) <$> columns', i + 1 )

        boundary = zipWith (padColumnWidth '-') maxColumnWidth (headers $> "")
        headers' = zipWith (padColumnWidth ' ') maxColumnWidth  headers
        columns' = zipWith (\w c -> padColumnWidth ' ' w <$> c) maxColumnWidth regColumns
        rowsVals = unfoldr genRow 0

        limiting = ("|" <>) . (<> "|") . T.intercalate "|"
    in  T.unlines . fmap limiting $
            [ boundary
            , headers'
            , boundary
            ] <> rowsVals


asCode :: Text -> Text
asCode = ("`" <>) . (<> "`")


txtLen :: Enum e => Text -> e
txtLen = toEnum . T.length


maximumWidth :: Foldable f => f Text -> Word
maximumWidth = maximumUsing txtLen


maximumUsing :: (Enum e, Foldable f, Ord e)  => (a -> e) -> f a -> e
maximumUsing f = maybe (toEnum 0) getMax . foldMap (Just . Max . f)


buildMeasurement :: BenchmarkMetadata -> IntMap BenchmarkSeriesRow -> BenchmarkSeriesMeasurement
buildMeasurement x = BenchmarkSeriesMeasurement . Arg x . BenchmarkSeriesTable


breakMeasurement :: BenchmarkSeriesMeasurement -> (BenchmarkMetadata, IntMap BenchmarkSeriesRow)
breakMeasurement (BenchmarkSeriesMeasurement (Arg meta (BenchmarkSeriesTable rows))) = (meta, rows)


digestBenchmarkFileContent :: BenchmarkFileContent -> BenchmarkSeriesSet -> BenchmarkSeriesSet
digestBenchmarkFileContent bfc (BenchmarkSeriesSet mapping) =
    let idx = extractBenchmarkIndex bfc
        val = extractBenchmarkRow bfc
        key = forgeKey idx
        row = forgeNum idx

        digestContent :: Maybe BenchmarkSeriesMeasurement -> Maybe BenchmarkSeriesMeasurement
        digestContent = Just . \case
            Nothing ->
                let meta = extractBenchmarkMetadata bfc
                in  buildMeasurement meta $ singleton row val
            Just current ->
                let (meta, rows) = breakMeasurement current
                in  buildMeasurement meta $ insert row val rows
    in  BenchmarkSeriesSet $ alter digestContent key mapping


extractBenchmarkIndex :: BenchmarkFileContent -> BenchParameters
extractBenchmarkIndex = benchScriptParameters . extractedBenchScript


extractBenchmarkRow :: BenchmarkFileContent -> BenchmarkSeriesRow
extractBenchmarkRow =
    let compileFlags = directivesSelected . benchScriptDirectives . extractedBenchScript
        subModelInfo = fmap (BenchmarkSeriesSubModel <$> spinModel <*> spinMemory <*> spinTiming) . extractedBackMatter
    in  BenchmarkSeriesRow <$> compileFlags <*> subModelInfo


extractBenchmarkMetadata :: BenchmarkFileContent -> BenchmarkMetadata
extractBenchmarkMetadata =
    let create = BenchmarkMetadata <$> directivesConstant <*> directivesExperiment <*> runtimeFlags
        select = benchScriptDirectives . extractedBenchScript
    in  create . select


forgeKey :: BenchParameters -> BenchmarkSeriesKey
forgeKey = BenchmarkSeriesKey <$> benchVersion <*> benchProperty <*> benchMembers


forgeNum :: Enum e => BenchParameters -> e
forgeNum = toEnum . fromEnum . benchTaskID


colateBenchmarkSeries :: Foldable f => f BenchmarkFileContent -> BenchmarkSeriesSet
colateBenchmarkSeries = foldr digestBenchmarkFileContent (BenchmarkSeriesSet mempty)

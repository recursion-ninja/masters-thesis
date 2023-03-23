{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}

module Thesis.Benchmark.Set
  ( -- * Data-types
    BenchmarkSeriesSet(..)
  , BenchmarkSeriesKey(..)
  , BenchmarkFileContent(..)
  , BenchmarkSeriesTable(..)
  , BenchmarkMetadata(..)
  , BenchmarkSeriesRow(..)
    -- ** Constructor
  , colateBenchmarkSeries
    -- ** Accessor
  , extractBenchmarkIndex
  , extractBenchmarkMetadata
  , extractBenchmarkRow
  ) where


import Data.Functor (($>))
import Data.Foldable (toList)
import Data.IntMap.Strict (IntMap, insert, singleton)
import Data.List (sort, transpose, unfoldr)
import Data.Map.Strict (Map, alter, toAscList)
--import Data.Maybe (fromMaybe, maybe)
import Data.Ratio
import Data.Semigroup (Arg(..), Max(..))
import Data.Text (Text)
import Data.Text qualified as T
import GHC.Exts (IsString(fromString))
--import Numeric.Natural
import Parser.SPIN.Types(BackMatter(..), RuntimeBody(..), SpinMemory(..), SpinModel(..), SpinTiming(..))
import Parser.BenchScript.Types

import Thesis.Catalog.LTL
--import Thesis.Catalog.Membership
import Thesis.Catalog.Protocol
import Thesis.Catalog.Size


{- |
General input type from file parser.
-}
data  BenchmarkFileContent
    = BenchmarkFileContent
    { extractedBenchScript :: BenchScript
    , extractedRuntimeBody :: RuntimeBody
    , extractedBackMatter  :: Maybe BackMatter
    } deriving (Show)


{- |
Nicely colated output type for consumption / pretty-printing.
-}
newtype BenchmarkSeriesSet = BenchmarkSeriesSet (Map BenchmarkSeriesKey BenchmarkSeriesMeasurement)


data  BenchmarkSeriesKey
    = BenchmarkSeriesKey
    { benchSeriesVersion  :: Protocol
    , benchSeriesProperty :: LTL
    , benchSeriesMembers  :: {-# UNPACK #-} Size
    } deriving (Eq, Ord)


newtype BenchmarkSeriesMeasurement = BenchmarkSeriesMeasurement (Arg BenchmarkMetadata BenchmarkSeriesTable)
    deriving (Eq, Ord)


data  BenchmarkMetadata
    = BenchmarkMetadata
    { benchSeriesDirectivesConstant   :: BenchDirectiveSet
    , benchSeriesDirectivesExperiment :: BenchDirectiveSet
    , benchSeriesRuntimeFlags         :: BenchRuntimeFlags
    } deriving (Eq, Ord)


newtype BenchmarkSeriesTable = BenchmarkSeriesTable (IntMap BenchmarkSeriesRow)


data  BenchmarkSeriesRow
    = BenchmarkSeriesRow
    { benchChosenFlags   :: BenchDirectiveSet
    , benchMaybeSubModel :: Maybe BenchmarkSeriesSubModel
    } deriving (Show)


data  BenchmarkSeriesSubModel
    = BenchmarkSeriesSubModel
    { benchSeriesModel :: SpinModel
    , benchSeriesSpace :: SpinMemory
    , benchSeriesTime  :: SpinTiming
    } deriving (Show)


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


{-
Rendering functions
-}


rowObservation :: BenchmarkSeriesRow -> [Text]
rowObservation (BenchmarkSeriesRow flags maybeModel) =
    let getFlags :: BenchDirectiveSet -> Text
        getFlags (BenchDirectiveSet xs) = T.unwords $ toList xs

        absent =
            [ "SEGFAULT"
            , ""
            , ""
            , ""
            , ""
            , ""
            , ""
            , ""
            ]

        present (BenchmarkSeriesSubModel model space time) =
            let nat :: Show a => (SpinModel -> a) -> Text
                nat f = fromString . show $ f model

                rat :: Rational -> Text
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
    let columns = transpose $ rowObservation <$> toList im
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

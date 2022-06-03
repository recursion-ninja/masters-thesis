{-# Language DerivingStrategies #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}
{-# Language ScopedTypeVariables #-}

module Thesis.Batch.Scanner
    ( -- * Scanner type
      MarkdownScanner
      -- * Scanner error collection
    , ScanFault ()
      -- * Scan a Markdown stream into a 'BatchMandate'
    , markdownScanner
    ) where

import Control.Applicative (liftA3)
import Control.Foldl (FoldM(..))
import Control.Monad.State.Strict
import Data.Bifunctor (bimap, first)
import Data.Foldable
import Data.Functor (($>))
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map.Merge.Strict (SimpleWhenMatched, merge, preserveMissing, zipWithMatched)
import Data.Map.Strict (Map, keysSet, (!))
import Data.Map.Strict qualified as Map
import Data.Matrix.Unboxed (Matrix)
import Data.Matrix.Unboxed qualified as M
import Data.Set (Set, difference)
import Data.Set qualified as Set
import Data.String (IsString(..))
import Data.Text (Text, unpack)
import Data.Traversable.WithIndex
import Data.Validation
import Data.Vector.Unboxed (Unbox, Vector)
import Data.Vector.Unboxed qualified as V
import Text.MMark (parse, runScannerM)
import Text.MMark.Extension (Block(..), Bni, Inline(..), asPlainText, scannerM)
import Text.Megaparsec.Error (errorBundlePretty)
import Text.Read (readMaybe)
import Thesis.Batch.Catalog
import Thesis.Batch.Mandate.Type
import Thesis.Batch.Scanner.Fault
import Thesis.Batch.Tabular.Bounding
import Thesis.Batch.Tabular.Cell
import Thesis.Batch.Tabular.Numeric


data IntermediateTable a where
    TmpTable :: Unbox a => Bounding (Map LTL (Matrix a)) -> IntermediateTable a


newtype ScanCongest
    = ScanCon { scanCon :: Validation ScanFault ScanMapping }
    deriving stock (Show)


newtype ScanOption
    = ScanRef { _scanRef :: Maybe Option }


newtype ScanMapping
    = ScanMap { _scanMap :: Map Option NumericTableSet }
    deriving stock (Show)


type AccruedScannner = FilePath -> Text -> ScanCongest


type GradualScannner = ScanCongest -> State ScanOption ScanCongest


type MarkdownScanner = FilePath -> Text -> Validation ScanFault BatchMandate


type MergingScanner = ScanMapping -> Validation ScanFault BatchMandate


type OpenningScanner = FoldM (State ScanOption) Bni ScanCongest


instance Monoid ScanOption where

    mempty = ScanRef Nothing


instance Monoid ScanCongest where

    mempty = ScanCon $ pure mempty


instance Monoid ScanMapping where

    mempty = ScanMap mempty


instance Semigroup (IntermediateTable a) where

    (TmpTable x) <> (TmpTable y) = TmpTable $ accumulateLTLs x y


instance Semigroup ScanOption where

    lhs@(ScanRef Just{}) <> (ScanRef Nothing) = lhs
    _                    <> rhs               = rhs


instance Semigroup ScanCongest where

    lhs@(ScanCon x) <> rhs@(ScanCon y) = case (x, y) of
        (Failure a, Failure b) -> ScanCon . Failure $ a <> b
        (Failure{}, _        ) -> lhs
        (Success a, Success b) -> ScanCon . Success $ a <> b
        (_        , _        ) -> rhs


instance Semigroup ScanMapping where

    (ScanMap x) <> (ScanMap y) =
        let matching :: SimpleWhenMatched k NumericTableSet NumericTableSet NumericTableSet
            matching = zipWithMatched $ const (<>)
        in  ScanMap $ merge preserveMissing preserveMissing matching x y


deriving stock instance Show a => Show (IntermediateTable a)


accumulateLTLs
    :: Bounding (Map LTL (Matrix a)) -> Bounding (Map LTL (Matrix a)) -> Bounding (Map LTL (Matrix a))
accumulateLTLs (Bounding cols rows mapping) =
    let matching :: SimpleWhenMatched k a b a
        matching = zipWithMatched $ const const
    in  Bounding cols rows . merge preserveMissing preserveMissing matching mapping . boundedTableCells


markdownScanner :: MarkdownScanner
markdownScanner src txt = scanCon (accrualScanner src txt) `bindValidation` mergingScanner


accrualScanner :: AccruedScannner
accrualScanner file txt =
    let markdownParseError = fromString . errorBundlePretty
        parseTextualStream = first markdownParseError $ parse file txt
        scanMarkdownStream = toEither . scanCon . (`evalState` mempty) . (`runScannerM` openningScanner)

        occursWithinStream :: ScanMapping -> Either ScanFault ScanMapping
        occursWithinStream val@(ScanMap x)
            | mempty == x = Left . fromString $ "No labeled tables within " <> show file
            | otherwise   = Right val
    in  ScanCon . fromEither $ parseTextualStream >>= scanMarkdownStream >>= occursWithinStream


congestFailure :: ScanFault -> ScanCongest -> ScanCongest
congestFailure err = let failure = ScanCon $ Failure err in (<> failure)


congestTabular :: Option -> NumericTable -> ScanCongest -> ScanCongest
congestTabular ctx num =
    let success = ScanCon . Success . ScanMap $ Map.singleton ctx $ collectNumericTable num in (<> success)


scanDigestion :: ScanFault -> GradualScannner
scanDigestion acc = pure . congestFailure acc


scanIngestion :: NumericTable -> GradualScannner
scanIngestion tbl acc = get >>= \case
    (ScanRef (Just ctx)) -> pure $ congestTabular ctx tbl acc
    _                    -> "No predefined context for tabular input" `scanDigestion` acc


contextSwitch :: NonEmpty Inline -> GradualScannner
contextSwitch txt acc =
    let processHeader :: Validation ScanFault Option -> State ScanOption ScanCongest
        processHeader = \case
            Failure err -> err `scanDigestion` acc
            Success ctx -> let new = ScanRef $ Just ctx in put new $> acc
    in  processHeader . textualOption $ asPlainText txt


absorbTabular :: MarkdownRows -> GradualScannner
absorbTabular txt acc = fromValidation (`scanDigestion` acc) (`scanIngestion` acc) $ tabularNumbers txt


fromValidation :: (e -> b) -> (a -> b) -> Validation e a -> b
fromValidation f g = codiagonal . bimap f g


openningScanner :: OpenningScanner
openningScanner =
    let scanSeed :: State ScanOption ScanCongest
        scanSeed = put mempty $> mempty

        scanStep :: Bni -> GradualScannner
        scanStep = \case
            Heading1 txt -> contextSwitch txt
            Heading2 txt -> contextSwitch txt
            Heading3 txt -> contextSwitch txt
            Heading4 txt -> contextSwitch txt
            Heading5 txt -> contextSwitch txt
            Heading6 txt -> contextSwitch txt
            Table _ rows -> absorbTabular rows
            _            -> pure
    in  scannerM scanSeed $ flip scanStep


mergingScanner :: MergingScanner
mergingScanner m =
    let isZero :: Cell -> UseDFA
        isZero = enumUseDFA

        idFunc :: Cell -> Cell
        idFunc = id

        equals :: LTL -> LTL -> Bool
        equals = (==)

        truthy :: LTL -> LTL -> Bool
        truthy = const $ const True

        aλ     = buildIntermediate isZero equals completeSetOfLTLs
        bλ     = buildIntermediate idFunc equals completeSetOfLTLs
        cλ     = buildIntermediate idFunc truthy (Set.singleton "Anything")
    in  case splayIntermediates m of
        Success (x, y, z) -> liftA3 mergeIntermediates (aλ x) (bλ y) (cλ z)
        Failure err       -> Failure err


splayIntermediates :: ScanMapping -> Validation ScanFault (NumericTableSet, NumericTableSet, NumericTableSet)
splayIntermediates (ScanMap m) =
    let (remain, extras) = Map.partitionWithKey (\k _ -> k `elem` needed) m
        needed           = completeSetOfOptions
        misses           = needed `difference` keysSet remain
        addErr           = fromString $ "Adjunct specs: " <> show (toList $ Map.keysSet extras)
        rmvErr           = fromString $ "Missing specs: " <> show (toList misses)
    in  case (null extras, null misses) of
        (False, False) -> Failure $ addErr <> rmvErr
        (False, True ) -> Failure rmvErr
        (True , False) -> Failure addErr
        (True , True ) -> case take 3 $ toList m of
            [a, b, c] -> Success (a, b, c)
            _         -> Failure "Impossible"


mergeIntermediates
    :: IntermediateTable UseDFA -> IntermediateTable Cell -> IntermediateTable Cell -> BatchMandate
mergeIntermediates (TmpTable a) (TmpTable b) (TmpTable c) =
    let val = snd . Map.findMin $ boundedTableCells c
        f k = M.zip3 (boundedTableCells a ! k) (boundedTableCells b ! k) val
    in  Batch $ a $> Map.fromSet f completeSetOfLTLs


buildIntermediate
    :: forall v
     . Unbox v
    => (Cell -> v)
    -> (LTL -> LTL -> Bool)
    -> Set LTL
    -> NumericTableSet
    -> Validation ScanFault (IntermediateTable v)
buildIntermediate trans check tags tables =
    let checkTableSet
            :: LTL
            -> Bounding (Matrix Cell)
            -> (Set LTL, Validation ScanFault (Bounding (Map LTL (Matrix v))))
            -> (Set LTL, Validation ScanFault (Bounding (Map LTL (Matrix v))))
        checkTableSet tag table (set, acc) = case Set.maxView set of
            Just (name, less) | tag `check` name ->
                let next :: Validation ScanFault (Bounding (Map LTL (Matrix v)))
                    next = Success $ fmap (Map.singleton tag . M.map trans) table
                in  (less, accumulateLTLs <$> next <*> acc)
            _ ->
                let errMsg = fromString $ "Unrecognized table tag: " <> show tag
                in  (set, first (errMsg <>) acc)

        buildSeed :: (Set LTL, Validation ScanFault (Bounding (Map LTL (Matrix v))))
        buildSeed = (tags, pure $ tableFst $> mempty)

        tableMap  = numTableSet tables

        tableFst :: Bounding (Matrix Cell)
        tableFst = snd $ Map.findMin tableMap
    in  fmap TmpTable . snd $ Map.foldrWithKey' checkTableSet buildSeed tableMap


tabularNumbers :: MarkdownRows -> Validation ScanFault NumericTable
tabularNumbers ((label :| colNums) :| rows) =
    let popRowIndex :: NonEmpty a -> ([a], [[a]]) -> ([a], [[a]])
        popRowIndex (idx :| row) (indices, gridRows) = (idx : indices, row : gridRows)

        (rowNums, grid) = foldr popRowIndex ([], []) rows

        colsCount :: Int
        colsCount = length colNums

        wordParse :: Read v => NonEmpty Inline -> Maybe v
        wordParse = readMaybe . unpack . asPlainText

        numError  = fold ["𝑥", "∉", "ℕ", ":"]

        lenError :: Show a => a -> String
        lenError i = fold [show i, "≠", "\8407j", ":"]

        makeError :: String -> String -> Maybe Int -> Maybe Int -> ScanFault
        makeError errorPref labelPref i j =
            let showIndex = maybe "*" show
            in  fromString $ unwords [errorPref, labelPref, "[", showIndex i, "]", "[", showIndex j, "]"]

        readIndex :: String -> Bool -> Int -> NonEmpty Inline -> Validation ScanFault Parameter
        readIndex pref isRowName i =
            let indexMay
                    | isRowName = (Just i, Nothing)
                    | otherwise = (Nothing, Just i)
                errorNote = uncurry (makeError numError pref) indexMay
            in  validate errorNote wordParse

        readColIndex = readIndex "Row#" False
        readRowIndex = readIndex "Col#" True
        readGridCell :: Int -> Int -> NonEmpty Inline -> Validation ScanFault Cell
        readGridCell i j =
            let errorNote = makeError numError "Cell" (Just i) (Just j) in validate errorNote wordParse

        toListVector = fmap (V.fromList . toList)

        toNameVector
            :: (Int -> NonEmpty Inline -> Validation ScanFault Parameter)
            -> [NonEmpty Inline]
            -> Validation ScanFault (Vector Parameter)
        toNameVector = (toListVector .) . itraverse

        toGridMatrix :: [[NonEmpty Inline]] -> Validation ScanFault (Matrix Cell)
        toGridMatrix =
            let f :: Int -> [NonEmpty Inline] -> Validation ScanFault (Vector Cell)
                f i xs =
                    let n         = length xs
                        errorNote = makeError (lenError n) "Row#" (Just i) Nothing
                        sameWidth :: p -> Maybe ()
                        sameWidth _
                            | colsCount == n = Just ()
                            | otherwise      = Nothing
                        validLength = validate errorNote sameWidth xs
                        validValues = V.fromList . toList <$> itraverse (readGridCell i) xs
                    in  validLength *> validValues
            in  fmap M.fromRows . itraverse f

        tagName = textualLTL $ asPlainText label
        valRows = toNameVector readRowIndex rowNums
        valCols = toNameVector readColIndex colNums
        valGrid = toGridMatrix grid
        valMake = Bounding <$> valCols <*> valRows <*> valGrid
    in  NumTable . (tagName, ) <$> valMake

{-# Language DerivingStrategies #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeApplications #-}

module Thesis.Batch.Scanner
    ( -- * Scanner type
      MarkdownScanner
      -- * Scanner error collection
    , ScanFault ()
      -- * Scan a Markdown stream into a 'BatchMandate'
    , markdownScanner
    ) where

import Commonmark (ParseError, SyntaxSpec, commonmarkWith, defaultSyntaxSpec)
import Commonmark.Extensions (gfmExtensions)
import Commonmark.Extensions.Attributes (attributesSpec, bracketedSpanSpec, fencedDivSpec, rawAttributeSpec)
import Commonmark.Extensions.Autolink (autolinkSpec)
import Commonmark.Extensions.DefinitionList (definitionListSpec)
import Commonmark.Extensions.FancyList (fancyListSpec)
import Commonmark.Extensions.Footnote (footnoteSpec)
import Commonmark.Extensions.Math (mathSpec)
import Commonmark.Extensions.PipeTable (pipeTableSpec)
import Commonmark.Extensions.Smart (smartPunctuationSpec)
import Commonmark.Pandoc
import Control.Applicative (liftA3)
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
import Text.Pandoc.Builder (Blocks, Inlines)
import Text.Pandoc.Definition
import Text.Read (readMaybe)
import Thesis.Batch.Catalog.LTL
import Thesis.Batch.Catalog.Option
import Thesis.Batch.Catalog.Size
import Thesis.Batch.Catalog.Time
import Thesis.Batch.Catalog.UseDFA
import Thesis.Batch.Mandate.Type
import Thesis.Batch.Scanner.Fault
import Thesis.Batch.Tabular.Bounding
import Thesis.Batch.Tabular.CellEntry
import Thesis.Batch.Tabular.Numeric


{-|
Scanner of a markdown stream
-}
type MarkdownScanner = FilePath -> Text -> Validation ScanFault BatchMandate


data IntermediateTable a where
    TmpTable :: Unbox a => Bounding (Map LTL (Matrix a)) -> IntermediateTable a


newtype ScanContext
    = ScanRef { scanRef :: Maybe Option }


newtype ScanMapping
    = ScanMap { _scanMap :: Map Option NumericTableSet }
    deriving stock (Show)


newtype ScanProduct
    = ScanCon { scanCon :: Validation ScanFault ScanMapping }
    deriving stock (Show)


type BlockScanner = Block -> GradualScanner


type GradualScanner = ScanProduct -> State ScanContext ScanProduct


type MergingScanner = ScanMapping -> Validation ScanFault BatchMandate


type StreamScannner = FilePath -> Text -> ScanProduct


instance Monoid ScanContext where

    mempty = ScanRef Nothing


instance Monoid ScanProduct where

    mempty = ScanCon $ pure mempty


instance Monoid ScanMapping where

    mempty = ScanMap mempty


instance Semigroup (IntermediateTable a) where

    (TmpTable x) <> (TmpTable y) = TmpTable $ accumulateLTLs x y


instance Semigroup ScanContext where

    lhs@(ScanRef Just{}) <> (ScanRef Nothing) = lhs
    _                    <> rhs               = rhs


instance Semigroup ScanProduct where

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


markdownScanner :: MarkdownScanner
markdownScanner src txt = scanCon (streamScanner src txt) `bindValidation` mergingScanner


{-|
Internal function
-}


streamScanner :: StreamScannner
streamScanner file txt =
    let parseTextualStream :: Either ScanFault Pandoc
        parseTextualStream = first fromString $ parseMarkdownPandoc file txt

        scanMarkdownStream = toEither . scanCon . pandocScanner

        occursWithinStream :: ScanMapping -> Either ScanFault ScanMapping
        occursWithinStream val@(ScanMap x)
            | mempty == x = Left . fromString $ "No labeled tables within " <> show file
            | otherwise   = Right val
    in  ScanCon . fromEither $ parseTextualStream >>= scanMarkdownStream >>= occursWithinStream


pandocScanner :: Pandoc -> ScanProduct
pandocScanner (Pandoc _ blocks) =
    let scanBlockStream :: State ScanContext ScanProduct -> ScanProduct
        scanBlockStream = flip evalState mempty

        scanStep :: BlockScanner
        scanStep =
            let bodyRows (TableBody _ _ hs rs) = hs <> rs

                cellText (Cell _ _ _ _ bs) = blockPlainText bs

                rowCellEntrys :: Row -> Validation ScanFault (NonEmpty Text)
                rowCellEntrys (Row _ []      ) = Failure $ fromString "Found: Row with zero columns"
                rowCellEntrys (Row _ [_     ]) = Failure $ fromString "Found: Row with one column"
                rowCellEntrys (Row _ (c : cs)) = Success $ cellText <$> c :| cs

                cellGrid :: [Row] -> [TableBody] -> [Row] -> Validation ScanFault (NonEmpty (NonEmpty Text))
                cellGrid hs bs fs = case fold [hs, foldMap bodyRows bs, fs] of
                    []     -> Failure $ fromString "Found: Table with zero rows"
                    [ _ ]  -> Failure $ fromString "Found: Table with one row"
                    r : rs -> traverse rowCellEntrys $ r :| rs

                transformState = \case
                    Header _ _ txt                                   -> contextSwitch txt
                    Table _ _ _ (TableHead _ hs) bs (TableFoot _ fs) -> absorbTabular $ cellGrid hs bs fs
                    _                                                -> pure
            in  transformState

        absorbTabular :: Validation ScanFault (NonEmpty (NonEmpty Text)) -> GradualScanner
        absorbTabular = \case
            Failure err -> scanDigestion err
            Success res -> fromValidation scanDigestion scanIngestion $ tabularNumbers res

        contextSwitch :: [Inline] -> GradualScanner
        contextSwitch txt =
            let processHeader :: Validation ScanFault Option -> GradualScanner
                processHeader = \case
                    Failure err -> scanDigestion err
                    Success ctx -> let newCtx = ScanRef $ Just ctx in (modify (const newCtx) $>)
            in  processHeader . textualOption $ inlinePlainText txt
    in  scanBlockStream $ foldlM (flip scanStep) mempty blocks


congestFailure :: ScanFault -> ScanProduct -> ScanProduct
congestFailure err = let failure = ScanCon $ Failure err in (<> failure)


congestTabular :: Option -> NumericTable -> ScanProduct -> ScanProduct
congestTabular ctx num =
    let success = ScanCon . Success . ScanMap $ Map.singleton ctx $ collectNumericTable num in (<> success)


scanDigestion :: ScanFault -> GradualScanner
scanDigestion err = pure . congestFailure err


scanIngestion :: NumericTable -> GradualScanner
scanIngestion tbl acc =
    let getStateRef :: State ScanContext (Maybe Option)
        getStateRef = scanRef <$> get
    in  getStateRef >>= \case
        Nothing  -> scanDigestion "No predefined context for tabular input" acc
        Just ctx -> pure $ congestTabular ctx tbl acc


fromValidation :: (e -> b) -> (a -> b) -> Validation e a -> b
fromValidation f g = codiagonal . bimap f g


mergingScanner :: MergingScanner
mergingScanner m =
    let isZero :: CellEntry -> UseDFA
        isZero = enumUseDFA

        idFunc :: CellEntry -> CellEntry
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
    :: IntermediateTable UseDFA -> IntermediateTable CellEntry -> IntermediateTable CellEntry -> BatchMandate
mergeIntermediates (TmpTable a) (TmpTable b) (TmpTable c) =
    let val = snd . Map.findMin $ boundedTableCellEntrys c
        f k = M.zip3 (boundedTableCellEntrys a ! k) (boundedTableCellEntrys b ! k) val
    in  Batch $ a $> Map.fromSet f completeSetOfLTLs


buildIntermediate
    :: forall v
     . Unbox v
    => (CellEntry -> v)
    -> (LTL -> LTL -> Bool)
    -> Set LTL
    -> NumericTableSet
    -> Validation ScanFault (IntermediateTable v)
buildIntermediate trans check tags tables =
    let checkTableSet
            :: LTL
            -> Bounding (Matrix CellEntry)
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

        tableFst :: Bounding (Matrix CellEntry)
        tableFst = snd $ Map.findMin tableMap
    in  fmap TmpTable . snd $ Map.foldrWithKey' checkTableSet buildSeed tableMap


accumulateLTLs
    :: Bounding (Map LTL (Matrix a)) -> Bounding (Map LTL (Matrix a)) -> Bounding (Map LTL (Matrix a))
accumulateLTLs (Bounding cols rows mapping) =
    let matching :: SimpleWhenMatched k a b a
        matching = zipWithMatched $ const const
    in  Bounding cols rows . merge preserveMissing preserveMissing matching mapping . boundedTableCellEntrys


tabularNumbers :: NonEmpty (NonEmpty Text) -> Validation ScanFault NumericTable
tabularNumbers ((label :| colNums) :| rows) =
    let popRowIndex :: NonEmpty a -> ([a], [[a]]) -> ([a], [[a]])
        popRowIndex (idx :| row) (indices, gridRows) = (idx : indices, row : gridRows)

        (rowNums, grid) = foldr popRowIndex ([], []) rows

        colsCount :: Int
        colsCount = length colNums

        wordParse :: Read v => Text -> Maybe v
        wordParse = readMaybe . unpack

        numError  = fold ["𝑥", "∉", "ℕ", ":"]

        lenError :: Show a => a -> String
        lenError i = fold [show i, "≠", "\8407j", ":"]

        makeError :: String -> String -> Maybe Int -> Maybe Int -> ScanFault
        makeError errorPref labelPref i j =
            let showIndex = maybe "*" show
            in  fromString $ unwords [errorPref, labelPref, "[", showIndex i, "]", "[", showIndex j, "]"]

        readIndex :: Read a => String -> Bool -> Int -> Text -> Validation ScanFault a
        readIndex pref isRowName i =
            let indexMay
                    | isRowName = (Just i, Nothing)
                    | otherwise = (Nothing, Just i)
                errorNote = uncurry (makeError numError pref) indexMay
            in  validate errorNote wordParse

        readColIndex = readIndex "Row#" False
        readRowIndex = readIndex "Col#" True
        readGridCellEntry :: Int -> Int -> Text -> Validation ScanFault CellEntry
        readGridCellEntry i j =
            let errorNote = makeError numError "CellEntry" (Just i) (Just j) in validate errorNote wordParse

        toListVector :: Unbox a => Validation ScanFault [a] -> Validation ScanFault (Vector a)
        toListVector = fmap (V.fromList . toList)

        toNameVector
            :: Unbox a => (Int -> Text -> Validation ScanFault a) -> [Text] -> Validation ScanFault (Vector a)
        toNameVector = (toListVector .) . itraverse

        toGridMatrix :: [[Text]] -> Validation ScanFault (Matrix CellEntry)
        toGridMatrix =
            let f :: Int -> [Text] -> Validation ScanFault (Vector CellEntry)
                f i xs =
                    let n         = length xs
                        errorNote = makeError (lenError n) "Row#" (Just i) Nothing
                        sameWidth :: p -> Maybe ()
                        sameWidth _
                            | colsCount == n = Just ()
                            | otherwise      = Nothing
                        validLength = validate errorNote sameWidth xs
                        validValues = V.fromList . toList <$> itraverse (readGridCellEntry i) xs
                    in  validLength *> validValues
            in  fmap M.fromRows . itraverse f

        tagName = textualLTL label
        valCols = toNameVector readColIndex colNums :: Validation ScanFault (Vector Size)
        valRows = toNameVector readRowIndex rowNums :: Validation ScanFault (Vector Time)
        valGrid = toGridMatrix grid
        valMake = Bounding <$> valCols <*> valRows <*> valGrid
    in  NumTable . (tagName, ) <$> valMake


blockPlainText :: [Block] -> Text
blockPlainText = foldMap $ \case
    Plain     is      -> inlinePlainText is
    Para      is      -> inlinePlainText is
    LineBlock is      -> foldMap inlinePlainText is
    CodeBlock _ txt   -> txt
    RawBlock  _ txt   -> txt
    BlockQuote bs     -> blockPlainText bs
    OrderedList _ bs  -> foldMap blockPlainText bs
    BulletList     bs -> foldMap blockPlainText bs
    DefinitionList xs -> foldMap (\(is, bs) -> inlinePlainText is <> foldMap blockPlainText bs) xs
    Header _ _ is     -> inlinePlainText is
    HorizontalRule    -> "\n"
    Table{}           -> mempty
    Div _ bs          -> blockPlainText bs
    Null              -> mempty


inlinePlainText :: [Inline] -> Text
inlinePlainText = foldMap $ \case
    Space           -> " "
    SoftBreak       -> "\n"
    LineBreak       -> "\n"
    Code      _ txt -> txt
    Math      _ txt -> txt
    RawInline _ txt -> txt
    Str         txt -> txt
    Emph        is  -> inlinePlainText is
    Underline   is  -> inlinePlainText is
    Strong      is  -> inlinePlainText is
    Strikeout   is  -> inlinePlainText is
    Superscript is  -> inlinePlainText is
    Subscript   is  -> inlinePlainText is
    SmallCaps   is  -> inlinePlainText is
    Span   _ is     -> inlinePlainText is
    Quoted _ is     -> inlinePlainText is
    Cite   _ is     -> inlinePlainText is
    Link  _ is _    -> inlinePlainText is
    Image _ is _    -> inlinePlainText is
    Note bs         -> blockPlainText bs


parseMarkdownPandoc :: FilePath -> Text -> Either String Pandoc
parseMarkdownPandoc fn s = do
    cmBlocks <- first show $ join $ commonmarkWith @(Either ParseError) fullMarkdownSpec fn s
    let blocks = toList . unCm @() @Blocks $ cmBlocks
    pure $ Pandoc mempty blocks


-- | GFM + official commonmark extensions
fullMarkdownSpec :: SyntaxSpec (Either ParseError) (Cm () Inlines) (Cm () Blocks)
fullMarkdownSpec = mconcat
    [ gfmExtensions
    , fancyListSpec
    , footnoteSpec
    , mathSpec
    , smartPunctuationSpec
    , definitionListSpec
    , attributesSpec
    , rawAttributeSpec
    , fencedDivSpec
    , bracketedSpanSpec
    , autolinkSpec
    , defaultSyntaxSpec
    ,
      -- as the commonmark documentation states, pipeTableSpec should be placed after
      -- fancyListSpec and defaultSyntaxSpec to avoid bad results when parsing
      -- non-table lines
      pipeTableSpec
    ]

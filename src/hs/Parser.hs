{-# Language OverloadedStrings #-}

module Parser
    ( extractRowFromFile
    , rowExtractor
    ) where

import BinaryUnit
import Control.Monad
import Data.Bifunctor (first)
import Data.ByteString.Lazy (ByteString, readFile, toStrict)
import Data.Char (chr, isAlpha, isAlphaNum, isPunctuation, isSpace)
import Data.Foldable
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.Functor.Identity
import Data.Scientific (toBoundedInteger)
import Data.String (fromString)
import Data.Time.Clock (DiffTime, secondsToDiffTime)
import Data.Void (Void)
import ExtractedRow
import Prelude hiding (readFile)
import Text.Megaparsec (ParsecT, optional, runParser, sepBy, takeWhile1P, takeWhileP, try)
import Text.Megaparsec.Byte
import Text.Megaparsec.Byte.Lexer
import Text.Megaparsec.Error (errorBundlePretty)


type RowParser = ParsecT Void ByteString Identity


extractRowFromFile :: FilePath -> IO (Either String ExtractedRow)
extractRowFromFile path = first errorBundlePretty . runParser rowExtractor path <$> readFile path


rowExtractor :: RowParser ExtractedRow
rowExtractor = do
    foundVersion     <- parseUntil lineContainingVersion
    (foundT, foundN) <- parseUntil lineContainingSecurityParams
    foundDirectives  <- parseUntil lineContainingDirectives
    foundProperty    <- parseUntil lineContainingProperty
    foundVectorLen   <- parseUntil lineContainingVectorLen
    foundStates      <- parseUntil lineContainingStates
    foundTransitions <- parseUntil lineContainingTransitions
    foundMemory      <- parseUntil lineContainingMemory
    foundRuntime     <- parseUntil lineContainingRuntime
    pure ExtractedRow
        { rowVersion     = foundVersion
        , rowProperty    = foundProperty & toStrict
        , rowSecurityT   = foundT
        , rowSecurityN   = foundN
        , rowRuntime     = foundRuntime
        , rowMemory      = foundMemory
        , rowVectorLen   = foundVectorLen
        , rowStates      = foundStates
        , rowTransitions = foundTransitions
        , rowDirectives  = foundDirectives <&> toStrict
        }


parseUntil :: RowParser a -> RowParser a
parseUntil target = do
    row <- optional $ try target
    case row of
        Just x  -> pure x
        Nothing -> consumeRow *> parseUntil target


consumeRow :: RowParser ()
consumeRow = takeWhileP (Just "ignored line content") (/= 10) *> void eol


lineContainingVersion :: RowParser Word
lineContainingVersion =
    let prefix = sequenceA_ [hspace, void $ string "CGKA version", hspace]
        notNum = \x -> isPunctuation x || isAlpha x
        title  = takeWhile1P (Just "version prefix") $ notNum . chr . fromIntegral
        suffix = sequenceA_ [hspace, void eol]
    in  prefix *> title *> decimal <* suffix


lineContainingProperty :: RowParser ByteString
lineContainingProperty =
    let prefix = sequenceA_
            [ hspace
            , void $ string "never claim"
            , hspace
            , void $ string "+"
            , hspace
            , void $ string "("
            , hspace
            ]
        suffix = sequenceA_ [void $ string ")", hspace, void eol]
    in  prefix *> identifier <* suffix


lineContainingSecurityParams :: RowParser (Word, Word)
lineContainingSecurityParams =
    let prefix = sequenceA_ [hspace, void $ string' "CGKA values", hspace, void $ string "(", hspace]
        demark = sequenceA_ [hspace, void $ string ",", hspace, void $ decimal, void $ string ",", hspace]
        suffix = sequenceA_ [hspace, void $ string ")", hspace, void eol]
        values = (,) <$> (decimal <* demark) <*> decimal
    in  prefix *> values <* suffix


lineContainingRuntime :: RowParser DiffTime
lineContainingRuntime =
    let prefix = sequenceA_ [hspace, void $ contiguous, hspace, void $ string' "runtime:", hspace]
        suffix = sequenceA_ [hspace, void eol]
        time :: Num a => Char -> RowParser a
        time c = decimal <* string (fromString [c]) <* hspace
        timing = constructRuntime <$> time 'd' <*> time 'h' <*> time 'm' <*> time 's'
    in  prefix *> timing <* suffix


lineContainingMemory :: RowParser MiB
lineContainingMemory =
    let prefix = hspace
        miByte = fromRational . toRational <$> scientific
        suffix = sequenceA_ [hspace, void $ string "total actual memory usage", hspace, void eol]
    in  prefix *> miByte <* suffix


lineContainingVectorLen :: RowParser Word
lineContainingVectorLen =
    let prefix = sequenceA_ [hspace, void $ string' "State-vector", hspace]
        -- State-vector 224 byte, depth reached 3149, errors: 0
        suffix = sequenceA_
            [ hspace
            , void $ string "byte, depth reached"
            , hspace
            , void decimal
            , void $ string ", errors:"
            , hspace
            , void decimal
            , hspace
            , void eol
            ]
    in  prefix *> decimal <* suffix


lineContainingStates :: RowParser Word
lineContainingStates =
    let prefix = hspace
        states = scientific >>= maybe (fail "Could not parse States") pure . toBoundedInteger
        suffix = sequenceA_
            [ hspace
            , void $ string "states, stored ("
            , void $ scientific
            , hspace
            , void $ string "visited)"
            , hspace
            , void eol
            ]
    in  prefix *> states <* suffix


lineContainingTransitions :: RowParser Word
lineContainingTransitions =
    let prefix = hspace
        shifts = scientific >>= maybe (fail "Could not parse Transitions") pure . toBoundedInteger
        suffix = sequenceA_ [hspace, void $ string "transitions (= visited+matched)", hspace, void eol]
    in  prefix *> shifts <* suffix


lineContainingDirectives :: RowParser [ByteString]
lineContainingDirectives =
    let prefix = sequenceA_ [hspace, void $ string' "Directives", hspace]
        suffix = hspace *> void eol
        values = (contiguous `sepBy` hspace)
    in  prefix *> values <* suffix


contiguous :: RowParser ByteString
contiguous = takeWhile1P (Just "contiguous inline word") (not . isSpace . chr . fromIntegral)


identifier :: RowParser ByteString
identifier = takeWhile1P (Just "alpha-numeric Identifier") (isAlphaNum . chr . fromIntegral)


constructRuntime :: Word -> Word -> Word -> Word -> DiffTime
constructRuntime d h m s =
    let daysNum = toInteger d
        daysRem = toInteger $ (h * 60 * 60) + (m * 60) + s
    in  secondsToDiffTime $ daysNum + daysRem

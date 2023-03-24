{-# Language FlexibleContexts #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}
{-# Language ScopedTypeVariables #-}

module Parser.SPIN.BackMatter
  ( pBackMatter
  ) where

import Control.Monad (filterM)
import Control.Monad.Combinators.NonEmpty (some)
import Data.Char (isSpace)
import Data.Foldable (toList)
import Data.Functor (void)
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe (isJust)
import Data.Proxy (Proxy(..))
import Data.Scientific (floatingOrInteger)
import Data.String (IsString)
import Data.Text (Text, unwords, words)
import Data.Void
import GHC.Exts (IsList(fromList), IsString(fromString))
import Numeric.Natural
import Parser.Internal (blankLine, endOfLine, lineContaining2, lineContaining3, lineContaining4, nextLine, restOfLine, valueLine)
import Parser.SPIN.Types
import Prelude hiding (unwords, words)
import Text.Megaparsec hiding (some)
import Text.Megaparsec.Char (char, hspace, hspace1)
import Text.Megaparsec.Char.Lexer (decimal, scientific, symbol)

import Text.Megaparsec.Debug

dbgP :: (MonadParsecDbg e s m, Show a) => String -> m a -> m a
--dbgP = dbg
dbgP = const id


{-
data  BackMatter
    = BackMatter
    { spinVersion   :: SpinVersion
    , spinOptions   :: SpinOptions
    , spinSearch    :: SpinSearch
    , spinModel     :: SpinModel
    , spinMemory    :: SpinMemory
    , spinUnreached :: SpinUnreached
    , spinTiming    :: SpinTiming
    }
-}


{-# INLINEABLE pBackMatter #-}
pBackMatter :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s BackMatter
pBackMatter =
    let sep :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s ()
        sep = dbgP "blank line(s) seperator" $ void $ some blankLine
    in  dbgP "pBackMatter" $ BackMatter
            <$>  pSpinVersion
            <*> (pSpinOptions   <* sep)
            <*> (pSpinSearch    <* sep)
            <*> (pSpinModel     <* sep)
            <*> (pSpinMemory    <* sep)
            <*> (pSpinUnreached <* sep)
            <*>  pSpinTiming


{-# INLINEABLE pSpinVersion #-}
pSpinVersion :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s SpinVersion
pSpinVersion =
    let pHead    = void $ chunk "(Spin Version"
        pTail    = void $ takeWhileP Nothing (/= '\n')
        pVersion = SpinVersion <$> (decimal <* char '.') <*> (decimal <* char '.') <*> decimal
        middle :: (a, b, c) -> b
        middle (_,x,_) = x
    in  dbgP "pSpinVersion" $ middle <$> lineContaining3 pHead pVersion pTail


{-# INLINEABLE pSpinOptions #-}
pSpinOptions :: forall s. (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s SpinOptions
pSpinOptions =
    let makeText :: Tokens s -> Text
        makeText = fromString . chunkToTokens (Proxy :: Proxy s)
    in  dbgP "pSpinOptions" $ SpinOptions . fmap makeText <$> some valueLine


{-# INLINEABLE pSpinSearch #-}
pSpinSearch :: forall s. (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s SpinSearch
pSpinSearch =
    let makeText :: Tokens s -> Text
        makeText = fromString . chunkToTokens (Proxy :: Proxy s)

        pSpinSearchHead :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s ()
        pSpinSearchHead = dbgP  "pSpinSearchHead" $ void nextLine

        pSpinSearchName :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s Text
        pSpinSearchName =
            let pSpinSearchWord :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s Text
                pSpinSearchWord = dbgP "pSpinSearchWord" $ makeText <$> takeWhile1P Nothing notFlagCharWord

                notFlagCharWord :: Char -> Bool
                notFlagCharWord = \case
                    '+' -> False
                    '-' -> False
                    c -> not $ isSpace c

            in  dbgP "pSpinSearchName" . fmap (unwords . toList) . some $ try (hspace *> pSpinSearchWord)
--            in  dbgP "pSpinSearchName" . fmap toStrict $ pSpinSearchWord


        pSpinSearchFlag :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s SpinSearchFlag
        pSpinSearchFlag = dbgP "pSpinSearchFlag" . fmap SpinSearchFlag $ (True <$ char '+') <|> (False <$ char '-')

        pSpinSearchText :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s Text
        pSpinSearchText = dbgP "pSpinSearchText" . parens $ makeText <$> takeWhile1P Nothing (/= ')')

        pSpinSearchLine =
            let gather = lineContaining3 pSpinSearchName pSpinSearchFlag pSpinSearchText
                reform :: (a, b, c) -> (a, (b, c))
                reform (x,y,z) = (x, (y, z))
            in  dbgP "pSpinSearchLine" $ reform <$> gather

        constructSearch :: Foldable f => f (Text, (SpinSearchFlag, Text)) -> SpinSearch
        constructSearch = SpinSearch . fromList . toList

    in  dbgP "pSpinSearch" $ constructSearch <$> (pSpinSearchHead *> some (try pSpinSearchLine))


{-# INLINEABLE pSpinModel #-}
pSpinModel :: forall s. (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s SpinModel
pSpinModel =
    let pBigNumber :: (Integral i, Show i, IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s i
        pBigNumber = either ceiling fromIntegral . floatingOrInteger <$> scientific

        pNamedNumber :: (Integral i, Show i, Stream s, Token s ~ Char) => Tokens s -> Parsec Void s i
        pNamedNumber str = dbgP "pNamedNumber" $ discard str *> hspace1 *> pBigNumber

        pLargeNumber :: (Stream s, Token s ~ Char) => Tokens s -> Parsec Void s Natural
        pLargeNumber = fmap fst . lineContaining2 (hspace *> pBigNumber) . discard

        pFirstLine = lineContaining3
            (pNamedNumber "State-vector")
            (pNamedNumber "byte, depth reached")
            (pNamedNumber "errors:")

        pStatesStored  = pLargeNumber "states, stored"
        pStatesMatched = pLargeNumber "states, matched"
        pTransitions   = pLargeNumber "transitions (= stored+matched)"
        pAtomicSteps   = pLargeNumber "atomic steps"

        pHashConflicts :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s (Maybe Natural)
        pHashConflicts =
            let get2 :: (a, b, c) -> b
                get2 (_,x,_) = x
            in  Just . get2 <$> lineContaining3 (discard "hash conflicts:") pBigNumber (discard "(resolved)")

        pHashGaveHint :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s Bool
        pHashGaveHint =
            let possibleLine = hspace *> void (chunk "hint: increase hashtable-size (-w) to reduce runtime") <* hspace <* endOfLine
            in  isJust <$> optional possibleLine

    in  dbgP "pSpinModel" $ (pFirstLine >>= \(vec, dep, err) -> SpinModel vec dep err
            <$> pStatesStored
            <*> pStatesMatched
            <*> pTransitions
            <*> pAtomicSteps
            <*> pHashConflicts
            <*> pHashGaveHint)


{-# INLINEABLE pSpinMemory #-}
pSpinMemory :: forall s. (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s SpinMemory
pSpinMemory =
    let pPreamble :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s ()
        pPreamble = discard "Stats on memory usage (in Megabytes):" <* endOfLine

        pMiBLine :: (Stream s, Token s ~ Char) => Tokens s -> Parsec Void s Rational
        pMiBLine strs =
            let valMiB = dbgP "valMiB" $ toRational <$> (hspace *> scientific)
                endStr = dbgP "endStr" . void $ chunk strs
                get1 :: (a, b, c) -> a
                get1 (x,_,_) = x
            in  get1 <$> lineContaining3 valMiB endStr (void restOfLine)

        check :: (Monad m, MonadParsec e s m)  => m a -> m ()
        check = lookAhead . try . void

        pOther :: (Stream s, Token s ~ Char) => [Tokens s] -> Parsec Void s Rational
        pOther opts =
            let makeOpt :: (Stream s, Token s ~ Char) => Int -> Tokens s -> Parsec Void s Rational
                makeOpt k v = try . dbgP ("Other " <> show k) . pMiBLine $ v

                powerset :: Foldable f  => f a -> [[a]]
                powerset = let f = [True, False] in filterM (const f) . toList

            in  fmap sum . choice $ fmap (\(k, v) -> try $ traverse (makeOpt k) v) . zip [0..] . powerset $ opts

    in  SpinMemory
            <$  (dbgP "Mem 1 head" ( pPreamble ))
            <*> (dbgP "Mem 2 <lex>" ( pMiBLine "equivalent memory usage for states" ))
            <*> (dbgP "Mem 3 <lex>" ((pMiBLine "actual memory usage for states" <* (check (pMiBLine "memory used for hash table") <|> void nextLine) )))
            <*> (dbgP "Mem 4 <lex>" ( pMiBLine "memory used for hash table" ))
            <*> (dbgP "Mem 5 <lex>" ( pMiBLine "memory used for DFS stack" ))
            <*> (dbgP "Mem 6 <lex>" ( pOther   ["other", "memory lost to"] ))
            <*> (dbgP "Mem 7 <lex>" ( pMiBLine "total actual memory" ))


{-# INLINEABLE pSpinUnreached #-}
pSpinUnreached :: forall s. (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s SpinUnreached
pSpinUnreached =
    let makeText :: Tokens s -> Text
        makeText = fromString . chunkToTokens (Proxy :: Proxy s)

        pSpinUnreachedLabel :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s SpinUnreachedLabel
        pSpinUnreachedLabel =
            let p = chunk "unreached in" *> hspace *> nextLine
            in  dbgP "pSpinUnreachedLabel" $ SpinUnreachedLabel . niceWords . makeText <$> p

        pSpinUnreachedLines :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s SpinUnreachedLines
        pSpinUnreachedLines =
            let pUnreachedLine :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s Text
                pUnreachedLine = dbgP "pUnreachedLine" $ niceWords . makeText <$> try (hspace1 *> nextLine)
            in  dbgP "pSpinUnreachedLines" $ SpinUnreachedLines <$> some pUnreachedLine

        pSpinKeyValuePairs :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s (NonEmpty (SpinUnreachedLabel, SpinUnreachedLines))
        pSpinKeyValuePairs =
            let pKVP = (,) <$> pSpinUnreachedLabel <*> pSpinUnreachedLines
            in  dbgP "pSpinKeyValuePairs" $ some pKVP

        constructUnreached :: NonEmpty (SpinUnreachedLabel, SpinUnreachedLines) -> SpinUnreached
        constructUnreached = SpinUnreached . fromList . toList

    in  constructUnreached <$> pSpinKeyValuePairs


{-# INLINEABLE pSpinTiming #-}
pSpinTiming :: forall s. (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s SpinTiming
pSpinTiming =
    let get3of4 :: (a, b, c, d) -> c
        get3of4 (_,_,x,_) = x

        valTiming :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s Rational
        valTiming = dbgP "valTiming" $ toRational <$> scientific

        pPanTimeLine :: (Stream s, Token s ~ Char) => Tokens s -> Parsec Void s Rational
        pPanTimeLine str = dbgP "pPanTimeLine" $ get3of4 <$> lineContaining4
            (dbgP "L4 <head>" $ void $ chunk "pan:")
            (dbgP "L4 <name>" $ void $ chunk str)
            (dbgP "L4 <secs>" $ valTiming)
            (dbgP "L4 <tail>" $ void restOfLine)

        pTimeElapsed     = pPanTimeLine "elapsed time"
        pRateStates      = pPanTimeLine "rate"
        pTransitionDelay = pPanTimeLine "avg transition delay"
    in  SpinTiming
            <$> (dbgP "pTimeElapsed" pTimeElapsed)
            <*> (dbgP "pRateStates" pRateStates)
            <*> (dbgP "pTransitionDelay" pTransitionDelay)


discard :: MonadParsec e s m => Tokens s -> m ()
discard = void . chunk


niceWords :: Text -> Text
niceWords = unwords . words


parens :: (IsString (Tokens s), MonadParsec e s m, Token s ~ Char) => m a -> m a
parens = between (symbol hspace "(") $ char ')'

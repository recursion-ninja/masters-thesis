{-# Language FlexibleContexts #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}

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
import Data.Scientific (floatingOrInteger)
import Data.String (IsString)
import Data.Text qualified as T
import Data.Text.Lazy (Text, toStrict, unwords, words)
import Data.Void
import GHC.Exts (IsList(fromList))
import Numeric.Natural
import Parser.Internal (blankLine, endOfLine, nextLine, restOfLine, valueLine)
import Parser.SPIN.Types
import Prelude hiding (unwords, words)
import Text.Megaparsec hiding (some)
import Text.Megaparsec.Char (char, hspace, hspace1)
import Text.Megaparsec.Char.Lexer (decimal, lexeme, scientific, symbol)

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
pBackMatter :: Parsec Void Text BackMatter
pBackMatter =
    let sep :: Parsec Void Text ()
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
pSpinVersion :: Parsec Void Text SpinVersion
pSpinVersion =
    let pHead    = void $ chunk "(Spin Version"
        pTail    = void $ takeWhileP Nothing (/= '\n')
        pVersion = SpinVersion <$> (decimal <* char '.') <*> (decimal <* char '.') <*> decimal
        middle :: (a, b, c) -> b
        middle (_,x,_) = x
    in  dbgP "pSpinVersion" $ middle <$> lineContaining3 pHead pVersion pTail


{-# INLINEABLE pSpinOptions #-}
pSpinOptions :: Parsec Void Text SpinOptions
pSpinOptions = dbgP "pSpinOptions" $ SpinOptions . fmap toStrict <$> some valueLine


{-# INLINEABLE pSpinSearch #-}
pSpinSearch :: Parsec Void Text SpinSearch
pSpinSearch =
    let pSpinSearchHead :: Parsec Void Text ()
        pSpinSearchHead = dbgP  "pSpinSearchHead" $ void nextLine

        pSpinSearchName :: Parsec Void Text T.Text
        pSpinSearchName =
            let pSpinSearchWord :: Parsec Void Text Text
                pSpinSearchWord = dbgP "pSpinSearchWord" $ takeWhile1P Nothing notFlagCharWord

                notFlagCharWord :: Char -> Bool
                notFlagCharWord = \case
                    '+' -> False
                    '-' -> False
                    c -> not $ isSpace c

            in  dbgP "pSpinSearchName" . fmap (toStrict . unwords . toList) . some $ try (hspace *> pSpinSearchWord)
--            in  dbgP "pSpinSearchName" . fmap toStrict $ pSpinSearchWord





        pSpinSearchFlag :: Parsec Void Text SpinSearchFlag
        pSpinSearchFlag = dbgP "pSpinSearchFlag" . fmap SpinSearchFlag $ (True <$ char '+') <|> (False <$ char '-')

        pSpinSearchText :: Parsec Void Text T.Text
        pSpinSearchText = dbgP "pSpinSearchText" . fmap toStrict . parens $ takeWhile1P Nothing (/= ')')

        pSpinSearchLine =
            let gather = lineContaining3 pSpinSearchName pSpinSearchFlag pSpinSearchText
                reform :: (a, b, c) -> (a, (b, c))
                reform (x,y,z) = (x, (y, z))
            in  dbgP "pSpinSearchLine" $ reform <$> gather

        constructSearch :: Foldable f => f (T.Text, (SpinSearchFlag, T.Text)) -> SpinSearch
        constructSearch = SpinSearch . fromList . toList

    in  dbgP "pSpinSearch" $ constructSearch <$> (pSpinSearchHead *> some (try pSpinSearchLine))


{-
data  SpinModel
    = SpinModel
    { stateVector   :: Word
    , searchDepth   :: Word
    , searchErrors  :: Word
    , statesStored  :: Natural
    , statesMatched :: Natural
    , transitions   :: Natural
    , atomicSteps   :: Natural
    , hashConflicts :: Maybe Word
    }
-}


{-# INLINEABLE pSpinModel #-}
pSpinModel :: Parsec Void Text SpinModel
pSpinModel =
    let bigNumber :: (Integral i, Show i) => Parsec Void Text i
        bigNumber = either ceiling fromIntegral . floatingOrInteger <$> scientific

        pNamedNumber :: (Integral i, Show i) => Text -> Parsec Void Text i
        pNamedNumber str = dbgP "pNamedNumber" $ discard str *> hspace1 *> bigNumber

        pLargeNumber :: Text -> Parsec Void Text Natural
        pLargeNumber = fmap fst . lineContaining2 (hspace *> bigNumber) . discard

        pFirstLine = lineContaining3
            (pNamedNumber "State-vector")
            (pNamedNumber "byte, depth reached")
            (pNamedNumber "errors:")

        pStatesStored  = pLargeNumber "states, stored"
        pStatesMatched = pLargeNumber "states, matched"
        pTransitions   = pLargeNumber "transitions (= stored+matched)"
        pAtomicSteps   = pLargeNumber "atomic steps"

        pHashConflicts :: Parsec Void Text (Maybe Natural)
        pHashConflicts =
            let get2 :: (a, b, c) -> b
                get2 (_,x,_) = x
            in  Just . get2 <$> lineContaining3 (discard "hash conflicts:") bigNumber (discard "(resolved)")

        pHashGaveHint :: Parsec Void Text Bool
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


{-
data  SpinMemory
    = SpinMemory
    { memEquivalent :: Word
    , memActual     :: Word
    , memHashTable  :: Word
    , memStackDFS   :: Word
    , memOtherUsed  :: Word
    , memTotalUsed  :: Word
    }
-}


{-# INLINEABLE pSpinMemory #-}
pSpinMemory :: Parsec Void Text SpinMemory
pSpinMemory =
    let pPreamble :: Parsec Void Text ()
        pPreamble = discard "Stats on memory usage (in Megabytes):" <* endOfLine

        pMiBLine :: Text -> Parsec Void Text Rational
        pMiBLine strs =
            let valMiB = dbgP "valMiB" $ toRational <$> (hspace *> scientific)
                endStr = dbgP "endStr" $ chunk strs
                get1 :: (a, b, c) -> a
                get1 (x,_,_) = x
            in  get1 <$> lineContaining3 valMiB endStr restOfLine

        check :: (Monad m, MonadParsec e s m)  => m a -> m ()
        check = lookAhead . try . void

        pOther :: [Text] -> Parsec Void Text Rational
        pOther opts =
            let makeOpt :: Int -> Text -> Parsec Void Text Rational
                makeOpt k v = try . dbgP ("Other " <> show k) $ pMiBLine v

                powerset :: (Foldable f, Show a)  => f a -> [[a]]
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
pSpinUnreached :: Parsec Void Text SpinUnreached
pSpinUnreached =
    let pSpinUnreachedLabel :: Parsec Void Text SpinUnreachedLabel
        pSpinUnreachedLabel =
            let p = chunk "unreached in" *> hspace *> nextLine
            in  dbgP "pSpinUnreachedLabel" $ SpinUnreachedLabel . niceWords <$> p

        pSpinUnreachedLines :: Parsec Void Text SpinUnreachedLines
        pSpinUnreachedLines =
            let pUnreachedLine :: Parsec Void Text T.Text
                pUnreachedLine = dbgP "pUnreachedLine" $ niceWords <$> try (hspace1 *> nextLine)
            in  dbgP "pSpinUnreachedLines" $ SpinUnreachedLines <$> some pUnreachedLine

        pSpinKeyValuePairs :: Parsec Void Text (NonEmpty (SpinUnreachedLabel, SpinUnreachedLines))
        pSpinKeyValuePairs =
            let pKVP = (,) <$> pSpinUnreachedLabel <*> pSpinUnreachedLines
            in  dbgP "pSpinKeyValuePairs" $ some pKVP

        constructUnreached :: NonEmpty (SpinUnreachedLabel, SpinUnreachedLines) -> SpinUnreached
        constructUnreached = SpinUnreached . fromList . toList

    in  constructUnreached <$> pSpinKeyValuePairs


{-
    = SpinTiming
    { timeElapsed     :: Word
    , rateStates      :: Rational
    , transitionDelay :: Rational
-}

{-# INLINEABLE pSpinTiming #-}
pSpinTiming :: Parsec Void Text SpinTiming
pSpinTiming =
    let get3of4 :: (a, b, c, d) -> c
        get3of4 (_,_,x,_) = x

        valTiming :: Parsec Void Text Rational
        valTiming = dbgP "valTiming" $ toRational <$> scientific

        pPanTimeLine :: Text -> Parsec Void Text Rational
        pPanTimeLine str = dbgP "pPanTimeLine" $ get3of4 <$> lineContaining4
            (dbgP "L4 <head>" $ chunk "pan:")
            (dbgP "L4 <name>" $ chunk str)
            (dbgP "L4 <secs>" $ valTiming)
            (dbgP "L4 <tail>" $ restOfLine)

        pTimeElapsed     = pPanTimeLine "elapsed time"
        pRateStates      = pPanTimeLine "rate"
        pTransitionDelay = pPanTimeLine "avg transition delay"
    in  SpinTiming
            <$> (dbgP "pTimeElapsed" pTimeElapsed)
            <*> (dbgP "pRateStates" pRateStates)
            <*> (dbgP "pTransitionDelay" pTransitionDelay)


--chomp :: (MonadParsec e s m, Token s ~ Char) => m ()
--chomp = space space1 empty empty


discard :: MonadParsec e s m => Tokens s -> m ()
discard = void . chunk


parens :: (IsString (Tokens s), MonadParsec e s m, Token s ~ Char) => m a -> m a
parens = between (symbol hspace "(") $ char ')'


niceWords :: Text -> T.Text
niceWords = toStrict . unwords . words


{-
lineContaining :: [Parsec Void Text a] -> [a]
lineContaining (p:|ps) =
    let sc = space (void spaceChar) empty empty
        finalItem = symbol sc
        singleton = const $ finalItem p
        plurality sc' =
            let otherItem = symbol sc'
                go (x:[]) = pure <$> finalItem x
                go (x:xs) = liftA2 (:) (otherItem x) $ go xs
            in  liftA2 (:|) (otherItem p) $ go ps

    in  lineFold sc $ case ps of
            [] -> singleton
            xs -> plurality
-}


inlineSep :: (MonadParsec e s m, Token s ~ Char) => Bool -> m ()
inlineSep x =
    let f :: (Token s ~ Char, MonadParsec e s m) => Bool -> m ()
        f True  = hspace1
        f False = hspace
    in  try (char ',' *> f x) <|> f x


lineContaining2
  :: ( Show a
     , Show b
     )
  => Parsec Void Text a
  -> Parsec Void Text b
  -> Parsec Void Text (a, b)
lineContaining2 a b = (,)
    <$  (dbgP "L2 lead" hspace)
    <*> (dbgP "L2 a <lex>" (lexeme (dbgP "L2 a <sep>" (inlineSep True )) (dbgP "L2 a <val>" a)) )
    <*> (dbgP "L2 b <lex>" (lexeme (dbgP "L2 b <sep>" (inlineSep False)) (dbgP "L2 b <val>" b)) )
    <*  (dbgP "L2 eol" endOfLine)


lineContaining3
  :: ( Show a
     , Show b
     , Show c
     )
  => Parsec Void Text a
  -> Parsec Void Text b
  -> Parsec Void Text c
  -> Parsec Void Text (a, b, c)
lineContaining3 a b c = (,,)
    <$  (dbgP "L3 lead" hspace)
    <*> (dbgP "L3 a <lex>" (lexeme (dbgP "L3 a <sep>" (inlineSep True )) (dbgP "L3 a <val>" a)) )
    <*> (dbgP "L3 b <lex>" (lexeme (dbgP "L3 b <sep>" (inlineSep True )) (dbgP "L3 b <val>" b)) )
    <*> (dbgP "L3 c <lex>" (lexeme (dbgP "L3 c <sep>" (inlineSep False)) (dbgP "L3 c <val>" c)) )
    <*  (dbgP "L3 eol" endOfLine)


lineContaining4
  :: Parsec Void Text a
  -> Parsec Void Text b
  -> Parsec Void Text c
  -> Parsec Void Text d
  -> Parsec Void Text (a, b, c, d)
lineContaining4 a b c d = (,,,)
    <$   hspace
    <*> (lexeme hspace1 a)
    <*> (lexeme hspace1 b)
    <*> (lexeme hspace1 c)
    <*> (lexeme hspace  d)
    <*   endOfLine


{-
lineContaining5
  :: Parsec Void Text a
  -> Parsec Void Text b
  -> Parsec Void Text c
  -> Parsec Void Text d
  -> Parsec Void Text e
  -> Parsec Void Text (a, b, c, d, e)
lineContaining5 a b c d e = lineFold chomp $ \chomp' -> (,,,,)
    <$> (lexeme chomp' a)
    <*> (lexeme chomp' b)
    <*> (lexeme chomp' c)
    <*> (lexeme chomp' d)
    <*> (lexeme chomp  e)


lineContaining6
  :: ( MonadParsec e s m
     , Token s ~ Char
     , TraversableStream s
     )
  => m a
  -> m b
  -> m c
  -> m d
  -> m e
  -> m f
  -> m (a, b, c, d, e, f)
lineContaining6 a b c d e f = lineFold chomp $ \chomp' -> (,,,,,)
    <$> (lexeme chomp' a)
    <*> (lexeme chomp' b)
    <*> (lexeme chomp' c)
    <*> (lexeme chomp' d)
    <*> (lexeme chomp' e)
    <*> (lexeme chomp  f)
-}

{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Parser.Internal
  ( double
  , endOfLine
  , fails
  -- ** Line stuff
  , blankLine
  , nextLine
  , valueLine
  , restOfLine
  -- ** Until combinators
  , anythingTill
  , somethingTill
  -- ** Set like operators
  , noneOfThese
  , someOfThese
  -- ** Line Containing
  , lineContaining2
  , lineContaining3
  , lineContaining4
  ) where

import Data.Foldable
import Data.Functor               (void)
import Data.List                  (sort)
import Data.List.NonEmpty         (nonEmpty)
import Data.Maybe                 (mapMaybe)
import Data.Set qualified as S
import Data.Text qualified as T
import Data.Text.Lazy qualified as LT
import Data.Vector.Unboxed        (Unbox, Vector, (!))
import Data.Vector.Unboxed qualified as V
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as LEX

--import Text.Megaparsec.Debug (dbg)
import Text.Megaparsec.Debug (MonadParsecDbg)


dbg
  :: (MonadParsecDbg e s m, Show a) => String -> m a -> m a
dbg = const id


{-# INLINEABLE blankLine #-}
{-# SPECIALISE blankLine :: Parsec Void  T.Text () #-}
{-# SPECIALISE blankLine :: Parsec Void LT.Text () #-}
{-# SPECIALISE blankLine :: Parsec Void  String () #-}
blankLine :: (MonadParsec e s m, Token s ~ Char) => m ()
blankLine = try (hspace *> endOfLine) <?> "blank line"


-- |
-- Parse a "line" of tokens.
{-# INLINEABLE nextLine #-}
{-# SPECIALISE nextLine :: Parsec Void  T.Text  T.Text #-}
{-# SPECIALISE nextLine :: Parsec Void LT.Text LT.Text #-}
{-# SPECIALISE nextLine :: Parsec Void  String  String #-}
nextLine :: (MonadParsec e s m, Token s ~ Char) => m (Tokens s)
nextLine = restOfLine <* endOfLine


-- |
-- Parse a "line" of tokens.
{-# INLINEABLE restOfLine #-}
{-# SPECIALISE restOfLine :: Parsec Void  T.Text  T.Text #-}
{-# SPECIALISE restOfLine :: Parsec Void LT.Text LT.Text #-}
{-# SPECIALISE restOfLine :: Parsec Void  String  String #-}
restOfLine :: (MonadParsec e s m, Token s ~ Char) => m (Tokens s)
restOfLine = takeWhileP Nothing isNotEOL


-- |
-- Parse a "line" of tokens.
{-# INLINEABLE valueLine #-}
{-# SPECIALISE valueLine :: Parsec Void  T.Text  T.Text #-}
{-# SPECIALISE valueLine :: Parsec Void LT.Text LT.Text #-}
{-# SPECIALISE valueLine :: Parsec Void  String  String #-}
valueLine :: (MonadParsec e s m, Token s ~ Char) => m (Tokens s)
valueLine = takeWhile1P Nothing isNotEOL <* endOfLine


-- |
-- Custom 'eol' combinator to account for /very/ old Mac file formats ending
-- lines in a single @\'\\r\'@.
{-# INLINE endOfLine #-}
{-# SPECIALISE endOfLine :: Parsec Void  T.Text () #-}
{-# SPECIALISE endOfLine :: Parsec Void LT.Text () #-}
{-# SPECIALISE endOfLine :: Parsec Void  String () #-}
endOfLine :: (Enum (Token s), MonadParsec e s m) => m ()
endOfLine =
    let pChar :: (Enum (Token s), MonadParsec e s m) => Char -> m ()
        pChar = void . single . enumCoerce
        nl = pChar '\n'
        cr = pChar '\r'
    in  nl <|> (cr *> nl)


isNotEOL :: Char -> Bool
isNotEOL = \case
            '\n' -> False
            '\r' -> False
            _    -> True


-- |
-- @anythingTill end@ consumes zero or more characters until @end@ is matched,
-- leaving @end@ in the stream.
{-# INLINEABLE anythingTill #-}
{-# SPECIALISE anythingTill :: Parsec Void  T.Text a -> Parsec Void  T.Text String #-}
{-# SPECIALISE anythingTill :: Parsec Void LT.Text a -> Parsec Void LT.Text String #-}
{-# SPECIALISE anythingTill :: Parsec Void  String a -> Parsec Void  String String #-}
anythingTill :: MonadParsec e s m => m a -> m [Token s]
anythingTill c = do
    ahead <- optional . try $ lookAhead c
    case ahead of
      Just _  -> pure []
      Nothing -> somethingTill c


-- |
-- @somethingTill end@ consumes one or more characters until @end@ is matched,
-- leaving @end@ in the stream.
{-# INLINEABLE somethingTill #-}
{-# SPECIALISE somethingTill :: Parsec Void  T.Text a -> Parsec Void  T.Text String #-}
{-# SPECIALISE somethingTill :: Parsec Void LT.Text a -> Parsec Void LT.Text String #-}
{-# SPECIALISE somethingTill :: Parsec Void  String a -> Parsec Void  String String #-}
somethingTill :: MonadParsec e s m => m a -> m [Token s]
somethingTill c = do
    _ <- notFollowedBy c
    (:) <$> anySingle <*> anythingTill c


-- |
-- Matches one or more elements from the supplied collection.
--
-- Coerces the collection to a sorted, unboxed vector and performs a binary
-- search on the elements to determine if a 'Token s' is part of the collection.
--
-- Preferable to 'Text.Megaparsec.someOf'.
{-# INLINE someOfThese #-}
{-# SPECIALISE someOfThese :: Foldable f => f Char -> Parsec Void  T.Text  T.Text #-}
{-# SPECIALISE someOfThese :: Foldable f => f Char -> Parsec Void LT.Text LT.Text #-}
{-# SPECIALISE someOfThese :: Foldable f => f Char -> Parsec Void  String  String #-}
{-# SPECIALISE someOfThese :: String -> Parsec Void  T.Text  T.Text #-}
{-# SPECIALISE someOfThese :: String -> Parsec Void LT.Text LT.Text #-}
{-# SPECIALISE someOfThese :: String -> Parsec Void  String  String #-}
someOfThese :: (Foldable f, MonadParsec e s m, Token s ~ a, Unbox a) => f a -> m (Tokens s)
someOfThese xs =
    let !uvec = V.fromList . sort $ toList xs
        !cond = withinVec uvec
    in  takeWhile1P Nothing cond


-- |
-- Matches one or more elements /not/ from the supplied collection.
--
-- Coerces the collection to a sorted, unboxed vector and performs a binary
-- search on the elements to determine if a 'Token s' is part of the collection.
--
-- Preferable to 'noneOf'.
{-# INLINE noneOfThese #-}
{-# SPECIALISE noneOfThese :: Foldable f => f Char -> Parsec Void  T.Text  T.Text #-}
{-# SPECIALISE noneOfThese :: Foldable f => f Char -> Parsec Void LT.Text LT.Text #-}
{-# SPECIALISE noneOfThese :: Foldable f => f Char -> Parsec Void  String  String #-}
{-# SPECIALISE noneOfThese :: String -> Parsec Void  T.Text  T.Text #-}
{-# SPECIALISE noneOfThese :: String -> Parsec Void LT.Text LT.Text #-}
{-# SPECIALISE noneOfThese :: String -> Parsec Void  String  String #-}
noneOfThese :: (Foldable f, MonadParsec e s m, Token s ~ a, Unbox a) => f a -> m (Tokens s)
noneOfThese xs =
    let !uvec = V.fromList . sort $ toList xs
        !cond = not . withinVec uvec
    in  takeWhile1P Nothing cond


-- |
-- Flexibly parses a 'Double' value represented in a variety of forms.
{-# INLINEABLE double #-}
{-# SPECIALISE double :: Parsec Void  T.Text Double #-}
{-# SPECIALISE double :: Parsec Void LT.Text Double #-}
{-# SPECIALISE double :: Parsec Void  String Double #-}
double :: (MonadParsec e s m, Token s ~ Char) => m Double
double = try real <|> fromIntegral <$> int
  where
     int  :: (MonadParsec e s m, Token s ~ Char) => m Integer
     int  = LEX.signed space LEX.decimal
     real = LEX.signed space LEX.float


-- |
-- Accepts zero or more Failure messages.
{-# INLINEABLE fails #-}
{-# SPECIALISE fails :: [String] -> Parsec Void  T.Text a #-}
{-# SPECIALISE fails :: [String] -> Parsec Void LT.Text a #-}
{-# SPECIALISE fails :: [String] -> Parsec Void  String a #-}
fails :: MonadParsec e s m => [String] -> m a
fails = failure Nothing . S.fromList . fmap Label . mapMaybe nonEmpty


-- |
-- Convert one Enum to another through the Int value.
enumCoerce :: (Enum a, Enum b) => a -> b
enumCoerce = toEnum . fromEnum


{-# INLINE withinVec #-}
{-# SPECIALISE withinVec :: Vector Char -> Char -> Bool #-}
withinVec :: (Ord a, Unbox a) => Vector a -> a -> Bool
withinVec v e = go 0 (V.length v - 1)
  where
    -- Perform a binary search on the unboxed vector
    -- to determine if a character is valid.
    --
    -- Equally fast, and uses less memory than a Set.
    {-# INLINE go #-}
    go !lo !hi
      | lo > hi   = False
      | otherwise = let !md = (hi + lo) `div` 2
                        !z  = v ! md
                    in  case z `compare` e of
                          EQ -> True
                          LT -> go    (md + 1) hi
                          GT -> go lo (md - 1)


inlineSep :: (MonadParsec e s m, Token s ~ Char) => Bool -> m ()
inlineSep x =
    let f :: (Token s ~ Char, MonadParsec e s m) => Bool -> m ()
        f True  = hspace1
        f False = hspace
    in  try (char ',' *> f x) <|> f x


{-# INLINEABLE lineContaining2 #-}
{-# SPECIALISE lineContaining2 :: (Show a, Show b) => Parsec Void  T.Text a -> Parsec Void  T.Text b -> Parsec Void  T.Text (a, b) #-}
{-# SPECIALISE lineContaining2 :: (Show a, Show b) => Parsec Void LT.Text a -> Parsec Void LT.Text b -> Parsec Void LT.Text (a, b) #-}
{-# SPECIALISE lineContaining2 :: (Show a, Show b) => Parsec Void  String a -> Parsec Void  String b -> Parsec Void  String (a, b) #-}
lineContaining2
  :: ( MonadParsecDbg e s m
     , Show a
     , Show b
     , Token s ~ Char
     )
  => m a
  -> m b
  -> m (a, b)
lineContaining2 a b = (,)
    <$  (dbg "L2 lead" hspace)
    <*> (dbg "L2 a <lex>" (LEX.lexeme (dbg "L2 a <sep>" (inlineSep True )) (dbg "L2 a <val>" a)) )
    <*> (dbg "L2 b <lex>" (LEX.lexeme (dbg "L2 b <sep>" (inlineSep False)) (dbg "L2 b <val>" b)) )
    <*  (dbg "L2 eol" endOfLine)


{-# INLINEABLE lineContaining3 #-}
{-# SPECIALISE lineContaining3 :: (Show a, Show b, Show c) => Parsec Void  T.Text a -> Parsec Void  T.Text b -> Parsec Void  T.Text c -> Parsec Void  T.Text (a,b,c) #-}
{-# SPECIALISE lineContaining3 :: (Show a, Show b, Show c) => Parsec Void LT.Text a -> Parsec Void LT.Text b -> Parsec Void LT.Text c -> Parsec Void LT.Text (a,b,c) #-}
{-# SPECIALISE lineContaining3 :: (Show a, Show b, Show c) => Parsec Void  String a -> Parsec Void  String b -> Parsec Void  String c -> Parsec Void  String (a,b,c) #-}
lineContaining3
  :: ( MonadParsecDbg e s m
     , Show a
     , Show b
     , Show c
     , Token s ~ Char
     )
  => m a
  -> m b
  -> m c
  -> m (a, b, c)
lineContaining3 a b c = (,,)
    <$  (dbg "L3 lead" hspace)
    <*> (dbg "L3 a <lex>" (LEX.lexeme (dbg "L3 a <sep>" (inlineSep True )) (dbg "L3 a <val>" a)) )
    <*> (dbg "L3 b <lex>" (LEX.lexeme (dbg "L3 b <sep>" (inlineSep True )) (dbg "L3 b <val>" b)) )
    <*> (dbg "L3 c <lex>" (LEX.lexeme (dbg "L3 c <sep>" (inlineSep False)) (dbg "L3 c <val>" c)) )
    <*  (dbg "L3 eol" endOfLine)


{-# INLINEABLE lineContaining4 #-}
{-# SPECIALISE lineContaining4 :: Parsec Void  T.Text a -> Parsec Void  T.Text b -> Parsec Void  T.Text c -> Parsec Void  T.Text d -> Parsec Void  T.Text (a,b,c,d) #-}
{-# SPECIALISE lineContaining4 :: Parsec Void LT.Text a -> Parsec Void LT.Text b -> Parsec Void LT.Text c -> Parsec Void LT.Text d -> Parsec Void LT.Text (a,b,c,d) #-}
{-# SPECIALISE lineContaining4 :: Parsec Void  String a -> Parsec Void  String b -> Parsec Void  String c -> Parsec Void  String d -> Parsec Void  String (a,b,c,d) #-}
lineContaining4
  :: ( MonadParsecDbg e s m
     , Token s ~ Char
     )
  => m a
  -> m b
  -> m c
  -> m d
  -> m (a, b, c, d)
lineContaining4 a b c d = (,,,)
    <$   hspace
    <*> (LEX.lexeme hspace1 a)
    <*> (LEX.lexeme hspace1 b)
    <*> (LEX.lexeme hspace1 c)
    <*> (LEX.lexeme hspace  d)
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
    <$> (LEX.lexeme chomp' a)
    <*> (LEX.lexeme chomp' b)
    <*> (LEX.lexeme chomp' c)
    <*> (LEX.lexeme chomp' d)
    <*> (LEX.lexeme chomp  e)


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
    <$> (LEX.lexeme chomp' a)
    <*> (LEX.lexeme chomp' b)
    <*> (LEX.lexeme chomp' c)
    <*> (LEX.lexeme chomp' d)
    <*> (LEX.lexeme chomp' e)
    <*> (LEX.lexeme chomp  f)
-}

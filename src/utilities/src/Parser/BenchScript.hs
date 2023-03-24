{-# Language FlexibleContexts #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}
{-# Language ScopedTypeVariables #-}

module Parser.BenchScript
  ( BenchScript(..)
  , BenchParameters(..)
  , pBenchScript
  ) where

--import Control.Monad.Combinators (someTill_)
import Control.Monad.Combinators.NonEmpty (some)
--import Data.Bifunctor (first)
--import Data.Char (isSpace)
--import Data.Foldable (toList)
import Data.Functor (($>), void)
import Data.List.NonEmpty (NonEmpty, sort)
import Data.Proxy (Proxy(..))
--import Data.Scientific (floatingOrInteger)
import Data.String (IsString(fromString))
import Data.Text (Text) --, unwords, words)
import Data.Void
--import GHC.Exts (IsList(fromList))
--import Numeric.Natural
import Parser.Internal
import Parser.BenchScript.Types
import Prelude hiding (unwords, words)
import Text.Megaparsec hiding (some)
import Text.Megaparsec.Char (char, hspace) --, hspace1)
import Text.Megaparsec.Char.Lexer (decimal) --, lexeme, scientific, symbol)
import Thesis.Catalog (LTL(..), Size)

import Text.Megaparsec.Debug


dbgP :: (MonadParsecDbg e s m, Show a) => String -> m a -> m a 
--dbgP = dbg
dbgP = const id

 
{-# INLINEABLE pBenchScript #-}
pBenchScript :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s BenchScript
pBenchScript =
    let pBenchScriptPrefix = anythingTill pBenchTaskID
        pBenchScriptMiddle = anythingTill $ chunk benchDirectivesStartingString
        pBenchScriptSuffix = anythingTill blankLine *> blankLine
    in  dbgP "BenchScript" $ BenchScript
            <$  pBenchScriptPrefix
            <*> pBenchParameters
            <*  pBenchScriptMiddle
            <*> pBenchDirectives
            <*  pBenchScriptSuffix
--            <*> (pBenchParameters <* (anythingTill pBenchDirectives))


pBenchTaskID :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s Word
pBenchTaskID = chunk "SLURM_ARRAY_TASK_ID" *> char '=' *> decimal <* endOfLine


benchDirectivesStartingString :: IsString s => s
benchDirectivesStartingString = "C -- (constant directives):"


pBenchParameters :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s BenchParameters
pBenchParameters =
    let pParameterLine :: (IsString (Tokens s), Show a, Stream s, Token s ~ Char, VisualStream s) => Tokens s -> Parsec Void s a -> Parsec Void s a
        pParameterLine x =
            let prefix = void $ chunk x
            in  fmap snd . lineContaining2 prefix

        pPropertyLTL   :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s LTL
        pPropertyLTL   = (chunk "FSU" $> FSU) <|> (chunk "PCS" $> PCS)

        pMembershipNum :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s Size
        pMembershipNum =
            let f = fmap (toEnum . fromEnum) :: Functor f => f Word -> f Size
            in  char 'N' *> char '=' *> f decimal

        pBenchProperty = pParameterLine "LTL property" pPropertyLTL
        pBenchMembers  = pParameterLine "CGKA members" pMembershipNum
        pBenchVersion  = pParameterLine "CGKA version" $ toEnum . pred <$> decimal
    in  dbgP "pBenchParameters" $ makeBenchParameters
            <$  (anythingTill pBenchTaskID)
            <*> (pBenchTaskID   <* anythingTill (void pBenchProperty))
            <*> (pBenchProperty <* anythingTill (void pBenchVersion))
            <*> (pBenchVersion  <* anythingTill (void pBenchMembers))
            <*> (pBenchMembers)


pBenchDirectives :: forall s. (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s BenchDirectives
pBenchDirectives =
    let pBenchOptionLines :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s (NonEmpty Text)
        pBenchOptionLines = dbgP "pBenchDirectives" $ sort <$> some pInlineCodeLine

        pBenchOptionSet :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => (NonEmpty Text -> b) -> Tokens s -> Parsec Void s b
        pBenchOptionSet f x = chunk x *> nextLine *> (f <$> pBenchOptionLines)

        pBenchStrategy = dbgP "pBenchStrategy" $ chunk "Strategy:" *> blankLine *> pInlineCodeLine

        -- "C -- (constant directives):"

        pBenchDirectiveSet :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Tokens s -> Parsec Void s BenchDirectiveSet
        pBenchDirectiveSet = pBenchOptionSet BenchDirectiveSet

        pBenchRuntimeFlags :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s BenchRuntimeFlags
        pBenchRuntimeFlags = pBenchOptionSet BenchRuntimeFlags "F -- (runtime flags):"

    in  dbgP "pBenchDirectives" $ BenchDirectives
          <$> pBenchDirectiveSet benchDirectivesStartingString
          <*> pBenchDirectiveSet "E -- (experiment directives):"
          <*> pBenchRuntimeFlags <* pBenchStrategy
          <*> pBenchDirectiveSet "Benchmarking selected directive set:"


pInlineCodeLine :: (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s Text
pInlineCodeLine = dbgP "pInlineCodeLine" $ try (hspace *> pInlineCode) <* blankLine


pInlineCode :: forall s. (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s Text
pInlineCode =
    let makeText :: Tokens s -> Text
        makeText = fromString . chunkToTokens (Proxy :: Proxy s)

        tick = '`'
        flag = char tick
        code = takeWhileP Nothing (/= tick)
    in  dbgP "pInlineCode" $ makeText <$> between flag flag code

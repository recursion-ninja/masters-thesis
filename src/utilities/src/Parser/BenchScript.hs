{-# Language FlexibleContexts #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}

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
--import Data.Scientific (floatingOrInteger)
--import Data.String (IsString)
import Data.Text qualified as T
import Data.Text.Lazy (Text, toStrict) --, unwords, words)
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
pBenchScript :: Parsec Void Text BenchScript
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


pBenchTaskID :: Parsec Void Text Word
pBenchTaskID = chunk "SLURM_ARRAY_TASK_ID" *> char '=' *> decimal <* endOfLine


benchDirectivesStartingString :: Text
benchDirectivesStartingString = "C -- (constant directives):"


pBenchParameters :: Parsec Void Text BenchParameters
pBenchParameters =
    let pParameterLine :: Show a => Text -> Parsec Void Text a -> Parsec Void Text a
        pParameterLine x = fmap snd . lineContaining2 (chunk x) 

        pPropertyLTL   :: Parsec Void Text LTL
        pPropertyLTL   = (chunk "FSU" $> FSU) <|> (chunk "PCS" $> PCS)

        pMembershipNum :: Parsec Void Text Size
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


pBenchDirectives :: Parsec Void Text BenchDirectives
pBenchDirectives =
    let pBenchOptionLines :: Parsec Void Text (NonEmpty T.Text)
        pBenchOptionLines = dbgP "pBenchDirectives" $ sort <$> some pInlineCodeLine

        pBenchOptionSet :: (NonEmpty T.Text -> b) -> Text -> Parsec Void Text b
        pBenchOptionSet f x = chunk x *> nextLine *> (f <$> pBenchOptionLines)

        pBenchStrategy = dbgP "pBenchStrategy" $ chunk "Strategy:" *> blankLine *> pInlineCodeLine

        -- "C -- (constant directives):"

        pBenchDirectiveSet :: Text -> Parsec Void Text BenchDirectiveSet
        pBenchDirectiveSet = pBenchOptionSet BenchDirectiveSet

        pBenchRuntimeFlags :: Parsec Void Text BenchRuntimeFlags
        pBenchRuntimeFlags = pBenchOptionSet BenchRuntimeFlags "F -- (runtime flags):"

    in  dbgP "pBenchDirectives" $ BenchDirectives
          <$> pBenchDirectiveSet benchDirectivesStartingString
          <*> pBenchDirectiveSet "E -- (experiment directives):"
          <*> pBenchRuntimeFlags <* pBenchStrategy
          <*> pBenchDirectiveSet "Benchmarking selected directive set:"


pInlineCodeLine :: Parsec Void Text T.Text
pInlineCodeLine = dbgP "pInlineCodeLine" $ try (hspace *> pInlineCode) <* blankLine


pInlineCode :: Parsec Void Text T.Text
pInlineCode =
    let tick = '`'
        flag = char tick
        code = takeWhileP Nothing (/= tick)
    in  dbgP "pInlineCode" $ toStrict <$> between flag flag code

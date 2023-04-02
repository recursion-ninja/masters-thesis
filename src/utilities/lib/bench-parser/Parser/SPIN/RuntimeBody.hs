{-# Language FlexibleContexts #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}
{-# Language ScopedTypeVariables #-}

module Parser.SPIN.RuntimeBody
  ( pRuntimeBody
  ) where

import Control.Monad.Combinators (someTill_)
import Data.Bifunctor (first)
import Data.List.NonEmpty
import Data.Proxy (Proxy(..))
import Data.String (IsString(fromString))
import Data.Text (Text, isInfixOf)
import Data.Void (Void)
import Parser.Internal (nextLine)
import Parser.SPIN.BackMatter (pBackMatter)
import Parser.SPIN.Types (BackMatter, RuntimeBody(..))
import Text.Megaparsec (Parsec, Stream, Token, Tokens, VisualStream, chunkToTokens, try)

import Text.Megaparsec.Debug

dbgP :: (MonadParsecDbg e s m, Show a) => String -> m a -> m a
--dbgP = dbg
dbgP = const id


{-# INLINEABLE pRuntimeBody #-}
pRuntimeBody :: forall s. (IsString (Tokens s), Stream s, Token s ~ Char, VisualStream s) => Parsec Void s (RuntimeBody, Maybe BackMatter)
pRuntimeBody =
    let makeBody  = RuntimeBody . fromList . fmap makeText

        makeText :: Tokens s -> Text
        makeText = fromString . chunkToTokens (Proxy :: Proxy s)
        
        pBoundary = dbgP "pBoundary" . try $ pSEGFAULT >>= \case
            False -> Just <$> dbgP "pBackMatter" pBackMatter 
            True  -> pure Nothing
        pSEGFAULT = dbgP "pSEGFAULT" ( (try nextLine) >>= pure . ("Segmentation fault" `isInfixOf`) . makeText )
    in  first makeBody <$> someTill_ nextLine pBoundary

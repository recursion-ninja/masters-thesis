{-# Language FlexibleContexts #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}

module Parser.SPIN.RuntimeBody
  ( pRuntimeBody
  ) where

import Control.Monad.Combinators (someTill_)
import Data.Bifunctor (first)
import Data.List.NonEmpty
import Data.Text.Lazy (Text, isInfixOf, toStrict)
import Data.Void (Void)
import Parser.Internal (nextLine)
import Parser.SPIN.BackMatter (pBackMatter)
import Parser.SPIN.Types (BackMatter, RuntimeBody(..))
import Text.Megaparsec (Parsec, try)

import Text.Megaparsec.Debug

dbgP :: (MonadParsecDbg e s m, Show a) => String -> m a -> m a
--dbgP = dbg
dbgP = const id

{-# INLINEABLE pRuntimeBody #-}
pRuntimeBody :: Parsec Void Text (RuntimeBody, Maybe BackMatter)
pRuntimeBody =
    let makeBody  = RuntimeBody . fromList . fmap toStrict
        pBoundary = dbgP "pBoundary" . try $ pSEGFAULT >>= \case
            False  -> Just <$> dbgP "pBackMatter" pBackMatter 
            True -> pure Nothing
        pSEGFAULT = dbgP "pSEGFAULT" ( (try nextLine) >>= pure . ("Segmentation fault" `isInfixOf`) )
    in  first makeBody <$> someTill_ nextLine pBoundary

{-# Language FlexibleContexts #-}

module Parser.SPIN.FrontMatter
  ( pFrontMatter
  ) where

import Data.Void (Void)
import Parser.SPIN.Types (FrontMatter(..))
import Text.Megaparsec (Parsec, Stream)

{-# INLINEABLE pFrontMatter #-}
pFrontMatter :: Stream s => Parsec Void s FrontMatter
pFrontMatter = pure . FrontMatter . pure $ mempty

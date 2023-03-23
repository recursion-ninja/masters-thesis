{-# Language FlexibleContexts #-}
{-# Language Safe #-}

module Parser.SPIN.FrontMatter
  ( pFrontMatter
  ) where

--import Data.List.NonEmpty
--import Data.Map.Strict
import Data.Text.Lazy (Text)
import Data.Void (Void)
import Parser.SPIN.Types (FrontMatter(..))

import Text.Megaparsec

-- newtype FrontMatter = FrontMatter (NonEmpty Text)

{-# INLINEABLE pFrontMatter #-}
pFrontMatter :: Parsec Void Text FrontMatter
pFrontMatter = pure . FrontMatter . pure $ mempty
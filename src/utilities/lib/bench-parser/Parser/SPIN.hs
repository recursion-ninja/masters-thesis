{-# Language DeriveAnyClass #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language OverloadedStrings #-}
{-# Language Strict #-}

module Parser.SPIN
  ( -- * SPIN Parsers
    pBackMatter
  , pFrontMatter
  , pRuntimeBody
    -- * SPIN Types
  , BackMatter(..)
  , FrontMatter(..)
  , RuntimeBody(..)
    -- ** SPIN Sub-types
  , SpinVersion(..)
  , SpinOptions(..)
  , SpinSearch(..)
  , SpinModel(..)
  , SpinMemory(..)
  , SpinUnreached(..)
  , SpinTiming(..)
  , SpinSearchFlag(..)
  , SpinUnreachedLabel(..)
  , SpinUnreachedLines(..)
  ) where

import Parser.SPIN.Types
import Parser.SPIN.BackMatter (pBackMatter)
import Parser.SPIN.FrontMatter (pFrontMatter)
import Parser.SPIN.RuntimeBody (pRuntimeBody)

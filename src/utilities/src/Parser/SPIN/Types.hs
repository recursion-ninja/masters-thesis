{-# Language DeriveAnyClass #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language OverloadedStrings #-}
{-# Language Strict #-}

module Parser.SPIN.Types
  ( BackMatter(..)
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

import Control.DeepSeq
import Data.List.NonEmpty
import Data.Map.Strict
import Data.Text (Text)
import GHC.Generics (Generic)
import Numeric.Natural (Natural)


newtype FrontMatter = FrontMatter (NonEmpty Text) deriving (Show)


newtype RuntimeBody = RuntimeBody (NonEmpty Text) deriving (Show)


data  BackMatter
    = BackMatter
    { spinVersion   :: SpinVersion
    , spinOptions   :: SpinOptions
    , spinSearch    :: SpinSearch
    , spinModel     :: SpinModel
    , spinMemory    :: SpinMemory
    , spinUnreached :: SpinUnreached
    , spinTiming    :: SpinTiming
    } deriving (Show)


data SpinVersion = SpinVersion Word Word Word deriving (Show)


newtype SpinOptions  = SpinOptions (NonEmpty Text) deriving (Show)


newtype SpinSearchFlag = SpinSearchFlag Bool deriving (Show)


newtype SpinSearch = SpinSearch (Map Text (SpinSearchFlag, Text)) deriving (Show)


data  SpinModel
    = SpinModel
    { stateVector   :: Word
    , searchDepth   :: Word
    , searchErrors  :: Word
    , statesStored  :: Natural
    , statesMatched :: Natural
    , transitions   :: Natural
    , atomicSteps   :: Natural
    , hashConflicts :: Maybe Natural
    , hashGaveHint  :: Bool
    } deriving (Show)


data  SpinMemory
    = SpinMemory
    { memEquivalent :: Rational
    , memActual     :: Rational
    , memHashTable  :: Rational
    , memStackDFS   :: Rational
    , memOtherUsed  :: Rational
    , memTotalUsed  :: Rational
    } deriving (Show)


newtype SpinUnreachedLabel = SpinUnreachedLabel Text deriving (Eq, Ord, Show)


newtype SpinUnreachedLines = SpinUnreachedLines (NonEmpty Text) deriving (Show)


newtype SpinUnreached = SpinUnreached (Map SpinUnreachedLabel SpinUnreachedLines) deriving (Show)


data  SpinTiming
    = SpinTiming
    { timeElapsed     :: Rational
    , rateStates      :: Rational
    , transitionDelay :: Rational
    } deriving (Show)


deriving stock instance Generic BackMatter


deriving stock instance Generic FrontMatter


deriving stock instance Generic RuntimeBody


deriving stock instance Generic SpinMemory


deriving stock instance Generic SpinModel


deriving stock instance Generic SpinOptions


deriving stock instance Generic SpinSearch


deriving stock instance Generic SpinSearchFlag


deriving stock instance Generic SpinTiming


deriving stock instance Generic SpinUnreached


deriving stock instance Generic SpinUnreachedLabel


deriving stock instance Generic SpinUnreachedLines


deriving stock instance Generic SpinVersion


deriving anyclass instance NFData BackMatter


deriving anyclass instance NFData FrontMatter


deriving anyclass instance NFData RuntimeBody


deriving anyclass instance NFData SpinMemory


deriving anyclass instance NFData SpinModel


deriving anyclass instance NFData SpinOptions


deriving anyclass instance NFData SpinSearch


deriving anyclass instance NFData SpinSearchFlag


deriving anyclass instance NFData SpinTiming


deriving anyclass instance NFData SpinUnreached


deriving anyclass instance NFData SpinUnreachedLabel


deriving anyclass instance NFData SpinUnreachedLines


deriving anyclass instance NFData SpinVersion

{-# Language Safe #-}

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

import Data.List.NonEmpty
import Data.Map.Strict
import Data.Text (Text)
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

{-# Language DeriveAnyClass #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language Strict #-}

module Parser.BenchScript.Types
  ( BenchScript(..)
  -- ** Sub-types
  , BenchParameters(..)
  , BenchDirectives(..)
  , BenchDirectiveSet(..)
  , BenchRuntimeFlags(..)
  -- ** Constructor
  , makeBenchParameters
  ) where

import Control.DeepSeq
import Data.List.NonEmpty (NonEmpty)
import Data.Text (Text)
import GHC.Generics (Generic)
import Thesis.Catalog (LTL(..), Protocol, Membership)


data  BenchScript
    = BenchScript
    { benchScriptParameters   :: BenchParameters
    , benchScriptDirectives   :: BenchDirectives
    } deriving (Show)


{-
data  BenchParameters
    = BenchParameters
    { benchTaskID   :: Word
    , benchProperty :: LTL
    , benchVersion  :: Word
    , benchMembers  :: Size
    } deriving (Show)
-}

data  BenchParameters
    = BenchParameters
    { benchVersion  :: Protocol
    , benchProperty :: LTL
    , benchMembers  :: Membership
    , benchTaskID   :: Word -- SLURM_ARRAY_TASK_ID
    } deriving (Eq, Ord)


newtype BenchRuntimeFlags = BenchRuntimeFlags (NonEmpty Text) deriving (Eq, Ord, Show)


newtype BenchDirectiveSet = BenchDirectiveSet (NonEmpty Text) deriving (Eq, Ord, Show)


data  BenchDirectives
    = BenchDirectives
    { directivesConstant   :: BenchDirectiveSet
    , directivesExperiment :: BenchDirectiveSet
    , runtimeFlags         :: BenchRuntimeFlags
    , directivesSelected   :: BenchDirectiveSet
    } deriving (Show)


deriving stock instance Generic BenchDirectives


deriving stock instance Generic BenchDirectiveSet


deriving stock instance Generic BenchParameters


deriving stock instance Generic BenchRuntimeFlags


deriving stock instance Generic BenchScript


deriving anyclass instance NFData BenchDirectives


deriving anyclass instance NFData BenchDirectiveSet


deriving anyclass instance NFData BenchParameters


deriving anyclass instance NFData BenchRuntimeFlags


deriving anyclass instance NFData BenchScript


instance Show BenchParameters where

    show (BenchParameters ver ltl size task) =
        let comma :: Show a => a -> String
            comma = (<> ",") . show
        in  unwords
            [ "("
            , comma ver
            , comma ltl
            , "N = " <> comma size
            , "ID = " <> show task
            , ")"
            ]


{- |
Construct 'BenchParameters' by permuting the parameters from the order they appear in the file to thier lexicographical ordering.
-}
makeBenchParameters :: (Enum t, Enum g) => t -> LTL -> Protocol -> g -> BenchParameters
makeBenchParameters task ltl ver limit =
    let enum :: (Enum a, Enum b) => a -> b
        enum = toEnum . fromEnum
    in  BenchParameters ver ltl (enum limit) (enum task)

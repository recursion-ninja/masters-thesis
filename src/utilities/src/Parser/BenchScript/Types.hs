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

import Data.List.NonEmpty (NonEmpty)
import Data.Text (Text)
import Thesis.Catalog (LTL(..), Protocol, Size)


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
    , benchMembers  :: Size
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
makeBenchParameters :: Word -> LTL -> Protocol -> Size -> BenchParameters
makeBenchParameters task ltl ver size = BenchParameters ver ltl size task

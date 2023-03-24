{-# Language DeriveAnyClass #-}
{-# Language DerivingStrategies #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language OverloadedStrings #-}

module Thesis.Catalog.Membership
    ( Membership ()
    ) where

import Control.DeepSeq
import Data.Ix
import Data.Word (Word8)
import GHC.Generics (Generic)


newtype Membership = Membership Word8


deriving stock instance Bounded Membership


deriving newtype instance Enum Membership


deriving stock instance Eq Membership


deriving stock instance Generic Membership


deriving newtype instance Integral Membership


deriving stock instance Ix Membership


deriving anyclass instance NFData Membership


deriving newtype instance Num Membership


deriving stock instance Ord Membership


deriving newtype instance Real Membership


instance Show Membership where

    show (Membership n) = "N=" <> show n

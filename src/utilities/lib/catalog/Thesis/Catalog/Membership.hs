{-# Language DerivingStrategies #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language OverloadedStrings #-}

module Thesis.Catalog.Membership
    ( Membership ()
    ) where

import Data.Ix
import Data.Word (Word8)


newtype Membership = Membership Word8


deriving stock instance Bounded Membership


deriving newtype instance Enum Membership


deriving stock instance Eq Membership


deriving newtype instance Integral Membership


deriving stock instance Ix Membership


deriving newtype instance Num Membership


deriving stock instance Ord Membership


deriving newtype instance Real Membership


instance Show Membership where

    show (Membership n) = "N=" <> show n

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE Strict #-}

module Thesis.Measure.VerificationError
  ( -- * Data-type
    VerificationError(..)
  ) where


-- | Types or reported errors from SPIN verification.
data  VerificationError
    = RuntimeSPIN
    | SEGFAULT
    | Counterexample
    | OutOfMemory
    deriving (Bounded, Enum, Eq, Ord, Show)

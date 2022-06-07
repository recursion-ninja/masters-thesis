{-# Language OverloadedStrings #-}
{-# Language Trustworthy #-}

module Thesis.Batch.Invoker
    ( InvokedOutput(..)
    , invokeCluster
    ) where

import Data.Foldable (fold)
import Data.List (intersperse)
import Data.String(IsString)
import Data.Text.Builder.Linear (Builder, runBuilder)
import Data.Text.IO (putStrLn)
import Prelude hiding (putStrLn)
import Thesis.Batch.Mandate
import Thesis.Batch.Printer.Class
import Thesis.Batch.Invoker.SubProcess


invokeCluster :: Parameterized -> Specification -> IO InvokedOutput
invokeCluster param@(ltl, row, col) specs@(minDFA, limMEM, lenVEC) =
    let renders :: (IsString a, Monoid a) => [a] -> a
        renders ks = "( " <> fold (intersperse ", " ks) <> " )"
        txtKeys = renders [ renderCell    ltl, renderCell    row, renderCell    col ] :: Builder
        txtVals = renders [ renderCell minDFA, renderCell limMEM, renderCell lenVEC ] :: Builder
    in  do
        putStrLn . runBuilder $ fold [ "  ", txtKeys, "    -->    ", txtVals ]
        makeClusterJob param specs <* putStrLn mempty

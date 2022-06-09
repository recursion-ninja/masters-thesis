{-# Language OverloadedStrings #-}
{-# Language Trustworthy #-}

module Thesis.Batch.Invoker
    ( InvokedOutput (..)
    , invokeCluster
    ) where

import Data.Foldable (fold)
import Data.List (intersperse)
import Data.String (IsString)
import Data.Text.Builder.Linear (Builder, runBuilder)
import Data.Text.IO (putStrLn)
import Prelude hiding (putStrLn)
import Thesis.Batch.Invoker.SubProcess
import Thesis.Batch.Mandate
import Thesis.Batch.Printer.Class


invokeCluster :: Parameterized -> Specification -> IO InvokedOutput
invokeCluster param@(ltl, row, col) specs@(minDFA, limMEM, lenVEC) =
    let renders :: (IsString a, Monoid a) => [a] -> a
        renders ks = "( " <> fold (intersperse ", " ks) <> " )"
        txtKeys = renders [renderCellEntry ltl, renderCellEntry row, renderCellEntry col] :: Builder
        txtVals = renders [renderCellEntry minDFA, renderCellEntry limMEM, renderCellEntry lenVEC] :: Builder
    in  do
        putStrLn . runBuilder $ fold ["  ", txtKeys, "    -->    ", txtVals]
        makeClusterJob param specs <* putStrLn mempty

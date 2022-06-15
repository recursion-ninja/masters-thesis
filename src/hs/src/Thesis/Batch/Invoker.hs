{-# Language OverloadedStrings #-}
{-# Language Trustworthy #-}

module Thesis.Batch.Invoker
    ( InvokedOutput (..)
    , invokeCluster
    ) where

import Data.Foldable (fold)
import Data.Functor (($>))
import Data.List (intersperse)
import Data.String (IsString(..))
import Data.Text.Builder.Linear (Builder, runBuilder)
import Data.Text.IO (putStrLn)
import Prelude hiding (putStrLn)
import System.Exit (ExitCode(..))
import Thesis.Batch.Invoker.SubProcess
import Thesis.Batch.Mandate
import Thesis.Batch.Printer.Class


invokeCluster :: Parameterized -> Specification -> IO InvokedOutput
invokeCluster param@(ltl, row, col) specs@(minDFA, limMEM, lenVEC) =
    let renders :: (IsString a, Monoid a) => [a] -> a
        renders ks = "( " <> fold (intersperse ", " ks) <> " )"

        txtKeys :: Builder
        txtKeys = renders [renderCellEntry ltl, renderCellEntry row, renderCellEntry col]

        txtVals :: Builder
        txtVals = renders [renderCellEntry minDFA, renderCellEntry limMEM, renderCellEntry lenVEC]

        txtInfo :: Builder
        txtInfo = fold [txtPref "Params", txtKeys, "    -->    ", txtVals]

        txtPads :: (Integral i, Show a) => i -> a -> Builder
        txtPads m v =
            let s = show v
                n = length s
            in  fromString $ replicate (fromIntegral m - n) ' ' <> s

        txtPref :: (IsString a, Semigroup a) => a -> a
        txtPref = ("  " <>) . (<> ": ")

        txtSent :: InvokedOutput -> Builder
        txtSent res =
            let txtSuffix :: Builder
                txtSuffix = case exitCode res of
                    ExitSuccess   -> "PASS"
                    ExitFailure c -> fold
                        [ "FAIL (", txtPads 3 c, ")\n"
                        , "  STDOUT:\n"
                        , exitOuts res
                        , "  STDERR:\n"
                        , exitErrs res
                        ]
            in  txtPref "Status" <> txtSuffix

        txtDump :: Builder -> IO ()
        txtDump = putStrLn . runBuilder
    in  do
        txtDump txtInfo
        makeClusterJob param specs >>= \res -> txtDump (txtSent res) *> putStrLn mempty $> res

{-# LANGUAGE OverloadedStrings #-}
--{-# LANGUAGE StrictData        #-}


module Thesis.Batch.Invoker.SubProcess
  ( -- * Process types
    InvokedOutput(..)
    -- * Process invokation
  , makeClusterJob
  ) where

--import Control.Applicative (liftA3)
import Data.Functor (($>))
import Data.Foldable
import Data.Text.Builder.Linear (Builder, fromDec, fromText, runBuilder)
import Data.Text.IO (hGetContents, putStrLn)
import Data.String(IsString(fromString))
import Prelude hiding (putStrLn)
import System.Exit (ExitCode(..))
import System.IO (Handle)
import System.Process
import Thesis.Batch.Mandate.Type


-- |
-- A data structure for storing the process and related paths.
data  InvokedOutput
    = InvokedOutput
    { exitErrs :: Builder
    , exitOuts :: Builder
    , exitCode :: ExitCode
    }


type ProcessStatus = (Maybe Handle, Maybe Handle, Maybe Handle, ProcessHandle)


instance Semigroup InvokedOutput where

    lhs <> rhs = InvokedOutput
        { exitErrs = exitErrs lhs   <>  exitErrs rhs
        , exitOuts = exitOuts lhs   <>  exitOuts rhs
        , exitCode = exitCode lhs `max` exitCode rhs
        }


-- |
-- Takes a 'FilePath' to a PCG script and executes an instance of PCG using the
-- script as the process's input.
--
-- Call 'destructProcess' on the supplied 'ScriptContext' afterwards to clean up
-- artifacts of the process.
makeClusterJob
    :: Parameterized
    -> Specification
    -> IO InvokedOutput
makeClusterJob param specs =
    let debugBefore :: IO ()
        debugBefore = putStrLn . runBuilder $ fold [ "  $ ", fromString makeCommand ]
--        debugBefore = pure ()

        debugExitCode :: ExitCode -> Builder
        debugExitCode ExitSuccess = "SUCCESS"
        debugExitCode (ExitFailure i) = fold [ "FAILURE [", fromDec i, "]" ]

        debugAfter :: InvokedOutput -> IO InvokedOutput
        debugAfter r =
            let reports =
                    [ "exitCode: " <> debugExitCode (exitCode r)
                    , "exitErrs: " <> exitErrs r
                    , "exitOuts: " <> exitOuts r
                    ]
            in  traverse_ (putStrLn . runBuilder) reports $> r
--        debugAfter = pure ()

        makeCommand = case cmdspec clusterJob of
            ShellCommand x -> x
            _ -> mempty

        clusterJob = constructClusterJob param specs

        sendOffJob = withCreateProcess clusterJob $ curry4 finalizer
    in  (debugBefore *> sendOffJob) >>= debugAfter


constructClusterJob
    :: Parameterized
    -> Specification
    -> CreateProcess
constructClusterJob (ltl, time, size) (minDFA, limMEM, lenVEC) =
    let makeOpt :: Show a => String -> a -> String
        makeOpt k v = k <> "=" <> show v
        
        makeCommand = unwords
            [ "make"
            , "clean"
            , "&&"
            , "make"
            , "cluster-verify"
            , makeOpt  "cores" 12
            , makeOpt "memory" limMEM
            , makeOpt "vector" lenVEC
            , makeOpt    "DFA" minDFA
            , makeOpt    "LTL" ltl
            , makeOpt      "T" time
            , makeOpt      "N" size
            ]

    in  CreateProcess
        { cmdspec            = ShellCommand makeCommand
        , cwd                = Nothing
        , env                = Nothing
        , std_in             = NoStream
        , std_out            = CreatePipe
        , std_err            = CreatePipe
        , close_fds          = True
        , create_group       = False
        , delegate_ctlc      = False
        , detach_console     = False
        , create_new_console = False
        , new_session        = False
        , child_group        = Nothing
        , child_user         = Nothing
        , use_process_jobs   = False
        }


curry4 :: ((a, b, c, d) -> e) -> a -> b -> c -> d -> e
curry4 f w x y z = f (w, x, y, z)


finalizer :: ProcessStatus -> IO InvokedOutput
finalizer (_, out, err, handle) = do
    eTxt <- getHandleOutput err
    oTxt <- getHandleOutput out
    let partial = InvokedOutput eTxt oTxt
    halt <- waitForProcess handle
    pure $ partial halt


getHandleOutput :: Maybe Handle -> IO Builder
getHandleOutput = maybe (pure mempty) (fmap fromText . hGetContents)

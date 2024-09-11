{-# language
    DataKinds
    , DeriveAnyClass
    , DerivingStrategies
    , FlexibleContexts
    , ImpredicativeTypes
    , ImportQualifiedPost
    , LambdaCase
    , NumericUnderscores
    , OverloadedStrings
    , PackageImports
    , ScopedTypeVariables
    , TypeApplications
    , TemplateHaskell
    , RecordWildCards
    , TupleSections
#-}

{-# options_ghc -fno-warn-gadt-mono-local-binds #-}

-- temporary
{-# options_ghc -Wwarn #-}

module Chainweb.Test.Pact5.RemotePactTest
    ( tests
    ) where

import Control.Monad.IO.Class (liftIO)
import Control.Exception (Exception)
import Chainweb.Test.Utils (testRetryPolicy)
import Pact.JSON.Encode qualified as J
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.Aeson qualified as Aeson
import Control.Monad.Catch (Handler(..), throwM)
import Data.List qualified as List
import Control.Retry
import Data.List.NonEmpty qualified as NE
import Data.List.NonEmpty (NonEmpty)
import Servant.Client
import Chainweb.Pact.RestAPI.Client
import Chainweb.Pact.Types
import Chainweb.ChainId
import "pact" Pact.Types.API qualified as Pact4
import "pact" Pact.Types.Command qualified as Pact4
import "pact" Pact.Types.Hash qualified as Pact4
import Chainweb.Graph (singletonChainGraph)
import Chainweb.Logger
import Chainweb.Mempool.Mempool (TransactionHash(..))
import Chainweb.Payload.PayloadStore
import Chainweb.Storage.Table.RocksDB
import Test.Tasty
import Control.Lens
import Test.Tasty.HUnit (assertBool, assertEqual, assertFailure, testCase)
import Chainweb.Test.Utils (ChainwebNetwork(..), NodeDbDirs(..), withNodesAtLatestBehavior, withNodeDbDirs, deadbeef)
import Control.Monad.Trans.Resource (ResourceT, runResourceT)
import PredicateTransformers as PT
--import Pact.Core.Command.RPC
import Pact.Core.Command.Types
import Pact.Core.Hash qualified as Pact5
import Chainweb.Version
import Chainweb.Test.TestVersions

{-
import Chainweb.Test.Cut.TestBlockDb (TestBlockDb (_bdbPayloadDb, _bdbWebBlockHeaderDb), addTestBlockDb, getCutTestBlockDb, getParentTestBlockDb, mkTestBlockDb, setCutTestBlockDb)
import Chainweb.Test.Pact4.Utils (stdoutDummyLogger, testPactServiceConfig, withBlockHeaderDb)
import Chainweb.Test.Pact5.CmdBuilder
import Chainweb.Test.Pact5.Utils
import Chainweb.Test.TestVersions
import Chainweb.Test.Utils
import Chainweb.Time
import Chainweb.Utils
import Chainweb.Utils (T2 (..), fromJuste)
import Chainweb.Utils.Serialization (runGetS, runPutS)
import Chainweb.Version
import Chainweb.WebBlockHeaderDB (getWebBlockHeaderDb)
import Chainweb.WebPactExecutionService
import Control.Concurrent
import Control.Concurrent.MVar
import Control.Exception (evaluate)
import Control.Exception.Safe
import Control.Lens hiding (only)
import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class
import Control.Monad.Reader
import Data.Aeson qualified as Aeson
import Data.ByteString (ByteString)
import Data.ByteString.Lazy qualified as LBS
import Data.Decimal
import Data.Default
import Data.Foldable
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product
import Data.Graph (Tree)
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.HashSet (HashSet)
import Data.IORef
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.MerkleLog (MerkleNodeType (..), merkleLeaf, merkleRoot, merkleTree)
import Data.Set qualified as Set
import Data.String (fromString)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Data.Text.IO qualified as T
import Data.Text.IO qualified as Text
import Data.Tree qualified as Tree
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import GHC.Stack
import Hedgehog hiding (Update)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import "pact" Pact.Types.Command qualified as Pact4
import "pact" Pact.Types.Hash qualified as Pact4
import Numeric.AffineSpace
import Pact.Core.Builtin
import Pact.Core.Capabilities
import Pact.Core.ChainData hiding (ChainId, _chainId)
import Pact.Core.Compile (CompileValue (..))
import Pact.Core.Errors
import Pact.Core.Evaluate
import Pact.Core.Gas.TableGasModel
import Pact.Core.Gas.Types
import Pact.Core.Gen
import Pact.Core.Info
import Pact.Core.Literal
import Pact.Core.Names
import Pact.Core.Names (ModuleName (ModuleName))
import Pact.Core.PactDbRegression
import Pact.Core.PactDbRegression qualified as Pact.Core
import Pact.Core.PactValue
import Pact.Core.Persistence
import Pact.Core.Persistence (PactDb (_pdbRead))
import Pact.Core.SPV (noSPVSupport)
import Pact.Core.Serialise
import Pact.Core.StableEncoding (encodeStable)
import Pact.Core.Verifiers
import Pact.Types.Gas qualified as Pact4
import Streaming.Prelude qualified as Stream
import System.LogLevel
import System.LogLevel (LogLevel (..))
import Test.Tasty.Hedgehog
import Text.Show.Pretty (pPrint)
import Text.Printf (printf)
import Control.Concurrent.Async (forConcurrently)
import Data.Bool
import System.IO.Unsafe
-}

data Fixture = Fixture
    { _fixtureNodeDbDirs :: [NodeDbDirs]
    , _fixtureNetwork :: ChainwebNetwork
    }
--makeLenses ''Fixture

fixtureClientEnv :: Getter Fixture ClientEnv
fixtureClientEnv = to $ \f -> _getServiceClientEnv $ _fixtureNetwork f

mkFixture :: RocksDb -> ResourceT IO Fixture
mkFixture baseRdb = do
    nodeDbDirs <- withNodeDbDirs baseRdb 1
    network <- withNodesAtLatestBehavior v id nodeDbDirs
    return $ Fixture
        { _fixtureNodeDbDirs = nodeDbDirs
        , _fixtureNetwork = network
        }

tests :: RocksDb -> TestTree
tests rdb = testGroup "Pact5 RemotePactTest"
    [ testCase "foo" (foo rdb)
    , testCase "pollingBadlistTest" (pollingBadlistTest rdb)
    ]

foo :: RocksDb -> IO ()
foo rdb = runResourceT $ do
    _fixture <- mkFixture rdb
    return ()

--polling
pollingBadlistTest :: RocksDb -> IO ()
pollingBadlistTest baseRdb = runResourceT $ do
    fixture <- mkFixture baseRdb
    let clientEnv = fixture ^. fixtureClientEnv

    liftIO $ do
        let rks = NE.fromList [pactDeadBeef]
        x <- polling clientEnv (NE.singleton pactDeadBeef)
        print x

newtype PollingException = PollingException String
    deriving stock (Show)
    deriving anyclass (Exception)

polling :: ()
    => ClientEnv
    -> NonEmpty RequestKey
    -> IO (HashMap RequestKey (CommandResult Aeson.Value Pact5.Hash))
polling clientEnv rks = do
    pollingWithDepth clientEnv rks Nothing

pollingWithDepth :: ()
    => ClientEnv
    -> NonEmpty RequestKey
    -> Maybe ConfirmationDepth
    -> IO (HashMap RequestKey (CommandResult Aeson.Value Pact5.Hash))
pollingWithDepth clientEnv rks mConfirmationDepth = do
    recovering testRetryPolicy [retryHandler] $ \iterNumber -> do
        putStrLn $ "pollingWithDepth: iteration " ++ show iterNumber

        let rksPact4 = NE.map toPact4RequestKey rks
        poll <- runClientM (pactPollWithQueryApiClient v cid mConfirmationDepth (Pact4.Poll rksPact4)) clientEnv
        case poll of
            Left e -> do
                throwM (PollingException (show e))
            Right (Pact4.PollResponses response) -> do
                return (convertPollResponse response)

    where
        retryHandler :: RetryStatus -> Handler IO Bool
        retryHandler _ = Handler $ \case
            PollingException _ -> return True
            _ -> return False

        toPact4RequestKey :: RequestKey -> Pact4.RequestKey
        toPact4RequestKey = \case
            RequestKey (Pact5.Hash bytes) -> Pact4.RequestKey (Pact4.Hash bytes)

        toPact5RequestKey :: Pact4.RequestKey -> RequestKey
        toPact5RequestKey = \case
            Pact4.RequestKey (Pact4.Hash bytes) -> RequestKey (Pact5.Hash bytes)

        toPact5CommandResult :: ()
            => Pact4.CommandResult Pact4.Hash
            -> CommandResult Aeson.Value Pact5.Hash
        toPact5CommandResult cr4 = case Aeson.eitherDecodeStrictText (J.encodeText cr4) of
            Left err -> error $ "toPact5CommandResult: decode failed: " ++ err
            Right cr5 -> cr5

        convertPollResponse :: ()
            => HashMap Pact4.RequestKey (Pact4.CommandResult Pact4.Hash)
            -> HashMap RequestKey (CommandResult Aeson.Value Pact5.Hash)
        convertPollResponse pact4Response = HashMap.fromList
            $ List.map (\(rk, cr) -> (toPact5RequestKey rk, toPact5CommandResult cr))
            $ HashMap.toList pact4Response

successfulTx :: Predicatory p => Pred p (CommandResult log err)
successfulTx = pt _crResult ? match _PactResultOk something

pactDeadBeef :: RequestKey
pactDeadBeef = case deadbeef of
    TransactionHash bytes -> RequestKey (Pact5.Hash bytes)

cid :: ChainId
cid = unsafeChainId 0

v :: ChainwebVersion
v = pact5InstantCpmTestVersion singletonChainGraph

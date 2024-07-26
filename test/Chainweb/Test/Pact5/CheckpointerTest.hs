{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NumericUnderscores #-}
module Chainweb.Test.Pact5.CheckpointerTest (tests) where

import Chainweb.BlockCreationTime
import Chainweb.BlockHeader
import Chainweb.Graph (singletonChainGraph)
import Chainweb.Logger
import Chainweb.MerkleLogHash
import Chainweb.MerkleUniverse (ChainwebMerkleHashAlgorithm)
import Chainweb.Pact.Backend.RelationalCheckpointer (initRelationalCheckpointer)
import Chainweb.Pact.Backend.SQLite.DirectV2 (close_v2)
import Chainweb.Pact.Backend.Utils
import Chainweb.Pact.Service.Types
import Chainweb.Pact.Types (defaultModuleCacheLimit)
import Chainweb.Pact.Utils (emptyPayload)
import qualified Chainweb.Pact4.TransactionExec
import Chainweb.Payload (PayloadWithOutputs_ (_payloadWithOutputsPayloadHash), Transaction (Transaction))
import Chainweb.Test.TestVersions
import Chainweb.Test.Utils
import Chainweb.Time
import Chainweb.Utils (fromJuste)
import Chainweb.Utils.Serialization (runGetS, runPutS)
import Chainweb.Version
import Control.Concurrent
import Control.Exception (evaluate)
import Control.Exception.Safe
import Control.Lens
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Resource
import Data.ByteString (ByteString)
import Data.Default
import Data.Foldable
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product
import Data.Graph (Tree)
import qualified Data.Map as Map
import Data.MerkleLog (MerkleNodeType (..), merkleLeaf, merkleRoot, merkleTree)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Tree as Tree
import Debug.Trace (traceM)
import Hedgehog hiding (Update)
import Hedgehog.Gen hiding (print)
import qualified Hedgehog.Range as Range
import Numeric.AffineSpace
import Pact.Core.Builtin
import Pact.Core.Evaluate (Info)
import Pact.Core.Gen
import Pact.Core.Literal
import Pact.Core.Names
import Pact.Core.PactDbRegression
import qualified Pact.Core.PactDbRegression as Pact.Core
import Pact.Core.PactValue
import Pact.Core.Persistence
import qualified Streaming.Prelude as Stream
import System.LogLevel
import Test.Tasty
import Test.Tasty.HUnit (assertEqual, testCase)
import Test.Tasty.Hedgehog
import Text.Show.Pretty
import Chainweb.Test.Pact5.Utils

-- | A @DbAction f@ is a description of some action on the database together with an f-full of results for it.
type DbValue = Integer
data DbAction f
    = forall k v. DbRead !T.Text RowKey (f (Either String (Maybe DbValue)))
    | forall k v. DbWrite WriteType !T.Text RowKey DbValue (f (Either String ()))
    | forall k v. DbKeys !T.Text (f (Either String [RowKey]))
    | forall k v. DbSelect !T.Text (f (Either String [(RowKey, Integer)]))
    | DbCreateTable T.Text (f (Either String ()))

data SomeDomain = forall k v. SomeDomain (Domain k v CoreBuiltin Info)

mkTableName :: T.Text -> TableName
mkTableName n = TableName n (ModuleName "mod" Nothing)

genDbAction :: Gen (DbAction (Const ()))
genDbAction = do
    let tn = choice [pure "A", pure "B", pure "C"]
    choice
        [ DbRead <$> tn <*> choice (pure . RowKey <$> ["A", "B", "C"]) <*> pure (Const ())
        , DbWrite
            <$> genWriteType
            <*> tn
            <*> choice (pure . RowKey <$> ["A", "B", "C"])
            <*> fmap fromIntegral (int (Range.constant 0 5))
            <*> pure (Const ())
        , DbKeys <$> tn <*> pure (Const ())
        , DbSelect <$> tn <*> pure (Const ())
        , DbCreateTable <$> tn <*> pure (Const ())
        ]
    where
    genWriteType = choice $ fmap pure
        [ Write
        , Insert
        , Update
        ]

-- a block is a list of actions
type DbBlock f = [DbAction f]

genDbBlock :: Gen (DbBlock (Const ()))
genDbBlock = list (Range.linear 1 20) genDbAction

genBlockHistory :: Gen [DbBlock (Const ())]
genBlockHistory = do
    let create tn = DbCreateTable tn (Const ())
    blocks <- list (Range.constant 1 20) genDbBlock
    -- we always start by making tables A and B to ensure the tests do something,
    -- but we leave table C uncreated to leave some room for divergent table sets
    return $ [create "A", create "B"] : blocks

hoistDbAction :: (forall a. (Eq a, Show a) => f a -> g a) -> DbAction f -> DbAction g
hoistDbAction f (DbRead tn k r) = DbRead tn k (f r)
hoistDbAction f (DbWrite wt tn k v r) = DbWrite wt tn k v (f r)
hoistDbAction f (DbKeys tn ks) = DbKeys tn (f ks)
hoistDbAction f (DbSelect tn rs) = DbSelect tn (f rs)
hoistDbAction f (DbCreateTable tn es) = DbCreateTable tn (f es)

tryShow :: IO a -> IO (Either String a)
tryShow = fmap (over _Left show) . tryAny

runDbAction :: Pact5Db -> DbAction (Const ()) -> IO (DbAction Identity)
runDbAction pactDb act =
    fmap (hoistDbAction (\(Pair (Const ()) fa) -> fa))
        $ runDbAction' pactDb act

extractInt :: RowData -> IO Integer
extractInt (RowData m) = evaluate (m ^?! ix (Field "k") . _PLiteral . _LInteger)

runDbAction' :: Pact5Db -> DbAction f -> IO (DbAction (Product f Identity))
runDbAction' pactDb = \case
    DbRead tn k v -> do
            maybeValue <- tryShow $ _pdbRead pactDb (DUserTables (mkTableName tn)) k
            integerValue <- (traverse . traverse) extractInt maybeValue
            return $ DbRead tn k $ Pair v (Identity integerValue)
    DbWrite wt tn k v s ->
        fmap (DbWrite wt tn k v . Pair s . Identity)
            $ tryShow $ ignoreGas def
            $ _pdbWrite pactDb wt (DUserTables (mkTableName tn)) k (RowData $ Map.singleton (Field "k") $ PLiteral $ LInteger v)
    DbKeys tn ks ->
        fmap (DbKeys tn . Pair ks . Identity)
            $ tryShow $ _pdbKeys pactDb (DUserTables (mkTableName tn))
    DbSelect tn rs ->
        fmap (DbSelect tn . Pair rs . Identity)
            $ tryShow $ do
                ks <- _pdbKeys pactDb (DUserTables (mkTableName tn))
                traverse (\k -> fmap (k,) . extractInt . fromJuste =<< _pdbRead pactDb (DUserTables (mkTableName tn)) k) ks
    DbCreateTable tn s ->
        fmap (DbCreateTable tn . Pair s . Identity)
            $ tryShow (ignoreGas def $ _pdbCreateUserTable pactDb (mkTableName tn))

-- craft a fake block header from txlogs, i.e. some set of writes.
-- that way, the block header changes if the write set stops agreeing.
blockHeaderFromTxLogs :: ParentHeader -> [TxLog ByteString] -> IO BlockHeader
blockHeaderFromTxLogs ph txLogs = do
    let
        logMerkleTree = merkleTree @ChainwebMerkleHashAlgorithm @ByteString
            [ TreeNode $ merkleRoot $ merkleTree
                [ InputNode (T.encodeUtf8 (_txDomain log))
                , InputNode (T.encodeUtf8 (_txKey log))
                , InputNode (_txValue log)
                ]
            | log <- txLogs
            ]
        encodedLogRoot = runPutS $ encodeMerkleLogHash $ MerkleLogHash $ merkleRoot logMerkleTree
    fakePayloadHash <- runGetS decodeBlockPayloadHash encodedLogRoot
    return $ newBlockHeader
        mempty
        fakePayloadHash
        (Nonce 0)
        (_blockCreationTime (_parentHeader ph) .+^ TimeSpan (1_000_000 :: Micros))
        ph

-- TODO things to test later:
-- that a tree of blocks can be explored, such that reaching any particular block gives identical results to running to that block from genesis

runBlocks
    :: Checkpointer GenericLogger
    -> ParentHeader
    -> [DbBlock (Const ())]
    -> IO [(BlockHeader, DbBlock Identity)]
runBlocks cp ph blks = do
    ((), finishedBlks) <- _cpRestoreAndSave cp (Just ph) $ traverse_ Stream.yield
        [ RunnableBlock $ \db _ph -> do
            pactDb <- assertDynamicPact5Db (_cpPactDbEnv db)
            _pdbBeginTx pactDb Transactional
            blk' <- traverse (runDbAction pactDb) blk
            txLogs <- _pdbCommitTx pactDb
            bh <- blockHeaderFromTxLogs (fromJuste _ph) txLogs
            return ([(bh, blk')], bh)
        | blk <- blks
        ]
    return finishedBlks

assertBlock :: Checkpointer GenericLogger -> ParentHeader -> (BlockHeader, DbBlock Identity) -> IO ()
assertBlock cp ph (expectedBh, blk) = do
    hist <- _cpReadFrom (_cpReadCp cp) (Just ph) $ \db -> do
        now <- getCurrentTimeIntegral
        pactDb <- assertDynamicPact5Db (_cpPactDbEnv db)
        _pdbBeginTx pactDb Transactional
        blk' <- forM blk (runDbAction' pactDb)
        txLogs <- _pdbCommitTx pactDb
        forM_ blk' $ \case
            DbRead d k (Pair expected actual) ->
                assertEqual "read result" expected actual
            DbWrite wt d k v (Pair expected actual) ->
                assertEqual "write result" expected actual
            DbKeys d (Pair expected actual) ->
                assertEqual "keys result" expected actual
            DbSelect d (Pair expected actual) ->
                assertEqual "select result" expected actual
            DbCreateTable tn (Pair expected actual) ->
                assertEqual "create table result" expected actual

        actualBh <- blockHeaderFromTxLogs ph txLogs
        assertEqual "block header" expectedBh actualBh
    throwIfNoHistory hist

tests = testGroup "Pact5 Checkpointer tests"
    [ withResourceT (liftIO . initCheckpointer v cid =<< withTempSQLiteResource) $ \cpIO ->
        testCase "valid PactDb before genesis" $ do
            cp <- cpIO
            _cpReadFrom (_cpReadCp cp) Nothing $ \db -> do
                pactDb <- assertDynamicPact5Db (_cpPactDbEnv db)
                Pact.Core.runPactDbRegression pactDb
            return ()
    , withResourceT (liftIO . initCheckpointer v cid =<< withTempSQLiteResource) $ \cpIO ->
        testProperty "linear block history validity" $ withTests 1000 $ property $ do
            blocks <- forAll genBlockHistory
            liftIO $ do
                cp <- cpIO
                -- extend this empty chain with the genesis block
                _cpRestoreAndSave cp Nothing $ Stream.yield $ RunnableBlock $ \_ _ ->
                    return ((), gh)
                -- run all of the generated blocks
                finishedBlocks <- runBlocks cp (ParentHeader gh) blocks
                let
                    finishedBlocksWithParents =
                        zip (fmap ParentHeader $ gh : (fst <$> finishedBlocks)) finishedBlocks
                -- assert that using readFrom to read from a parent, then executing the same block,
                -- gives the same results
                forM_ finishedBlocksWithParents $ \(ph, block) -> do
                    assertBlock cp ph block
    ]

v = pact5CheckpointerTestVersion singletonChainGraph
cid = unsafeChainId 0
gh = genesisBlockHeader v cid


instance (forall a. Show a => Show (f a)) => Show (DbAction f) where
    showsPrec n (DbRead tn k v) = showParen (n > 10) $
        showString "DbRead " . showsPrec 11 tn
        . showString " " . showsPrec 11 k
        . showString " " . showsPrec 11 v
    showsPrec n (DbWrite wt tn k v r) = showParen (n > 10) $
        showString "DbWrite " . showsPrec 11 wt
        . showString " " . showsPrec 11 tn
        . showString " " . showsPrec 11 k
        . showString " " . showsPrec 11 v
        . showString " " . showsPrec 11 r
    showsPrec n (DbKeys tn ks) = showParen (n > 10) $
        showString "DbKeys " . showsPrec 11 tn
        . showString " " . showsPrec 11 ks
    showsPrec n (DbSelect tn rs) = showParen (n > 10) $
        showString "DbSelect " . showsPrec 11 tn
        . showString " " . showsPrec 11 rs
    showsPrec n (DbCreateTable tn r) = showParen (n > 10) $
        showString "DbSelect " . showsPrec 11 tn
        . showString " " . showsPrec 11 r
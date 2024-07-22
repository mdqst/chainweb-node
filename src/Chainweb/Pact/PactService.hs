{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module: Chainweb.Pact.PactService
-- Copyright: Copyright © 2018,2019,2020 Kadena LLC.
-- License: See LICENSE file
-- Maintainers: Lars Kuhtz, Emily Pillmore, Stuart Popejoy
-- Stability: experimental
--
-- Pact service for Chainweb
--
module Chainweb.Pact.PactService
    ( initialPayloadState
    , execNewBlock
    , execContinueBlock
    , execValidateBlock
    , execTransactions
    , execLocal
    , execLookupPactTxs
    , execPreInsertCheckReq
    , execBlockTxHistory
    , execHistoricalLookup
    , execReadOnlyReplay
    , execSyncToBlock
    , runPactService
    , withPactService
    , execNewGenesisBlock
    , getGasModel
    ) where

import Control.Concurrent hiding (throwTo)
import Control.Concurrent.Async
import Control.Concurrent.STM
import Control.Exception (AsyncException(ThreadKilled))
import Control.Exception.Safe
import Control.Lens hiding ((:>))
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Primitive (PrimState)

import qualified Data.DList as DL
import Data.Either
import Data.Word (Word64)
import Data.Foldable (toList)
import Data.IORef
import qualified Data.HashMap.Strict as HM
import Data.LogMessage
import qualified Data.Map.Strict as M
import Data.Maybe
import Data.Monoid
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Data.Vector (Vector)
import qualified Data.Vector as V
import qualified Data.UUID as UUID
import qualified Data.UUID.V4 as UUID
import GrowableVector.Lifted (Vec)
import GrowableVector.Lifted qualified as Vec

import System.IO
import System.LogLevel

import Prelude hiding (lookup)

import qualified Streaming as Stream
import qualified Streaming.Prelude as Stream

import qualified Pact.Gas as P
import Pact.Gas.Table
import Pact.Interpreter(PactDbEnv(..))
import qualified Pact.JSON.Encode as J
import qualified Pact.Types.Command as P
import qualified Pact.Types.Hash as P
import qualified Pact.Types.RowData as P
import qualified Pact.Types.Runtime as P
import qualified Pact.Types.Pretty as P
import qualified Pact.Parse as P

import qualified Pact.Core.Builtin as Pact5
import qualified Pact.Core.Persistence as Pact5
import qualified Pact.Core.Gas as Pact5
import qualified Pact.Core.Gas.TableGasModel as Pact5

import qualified Chainweb.Pact4.TransactionExec as Pact4

import Chainweb.BlockHash
import Chainweb.BlockHeader
import Chainweb.BlockHeaderDB
import Chainweb.BlockHeight
import Chainweb.ChainId
import Chainweb.Logger
import Chainweb.Mempool.Mempool as Mempool
import Chainweb.Miner.Pact
import Chainweb.Pact.Backend.RelationalCheckpointer (withProdRelationalCheckpointer)
import Chainweb.Pact.Backend.Types
import Chainweb.Pact.PactService.Pact4.ExecBlock
import Chainweb.Pact.PactService.Checkpointer
import Chainweb.Pact.Service.PactQueue (PactQueue, getNextRequest)
import Chainweb.Pact.Service.Types
import Chainweb.Pact.SPV
import Chainweb.Pact.Types
import qualified Chainweb.Pact4.Validations as Pact4
import Chainweb.Payload
import Chainweb.Payload.PayloadStore
import Chainweb.Time
import qualified Chainweb.Pact4.Transaction as Pact4
import Chainweb.TreeDB
import Chainweb.Utils hiding (check)
import Chainweb.Version
import Chainweb.Version.Guards
import Utils.Logging.Trace
import Chainweb.Counter
import qualified Chainweb.Pact.PactService.Pact4.ExecBlock as Pact4


runPactService
    :: Logger logger
    => CanReadablePayloadCas tbl
    => ChainwebVersion
    -> ChainId
    -> logger
    -> Maybe (Counter "txFailures")
    -> PactQueue
    -> MemPoolAccess
    -> BlockHeaderDb
    -> PayloadDb tbl
    -> SQLiteEnv
    -> PactServiceConfig
    -> IO ()
runPactService ver cid chainwebLogger txFailuresCounter reqQ mempoolAccess bhDb pdb sqlenv config =
    void $ withPactService ver cid chainwebLogger txFailuresCounter bhDb pdb sqlenv config $ do
        initialPayloadState ver cid
        serviceRequests mempoolAccess reqQ

withPactService
    :: (Logger logger, CanReadablePayloadCas tbl)
    => ChainwebVersion
    -> ChainId
    -> logger
    -> Maybe (Counter "txFailures")
    -> BlockHeaderDb
    -> PayloadDb tbl
    -> SQLiteEnv
    -> PactServiceConfig
    -> PactServiceM logger tbl a
    -> IO (T2 a PactServiceState)
withPactService ver cid chainwebLogger txFailuresCounter bhDb pdb sqlenv config act = do
    withProdRelationalCheckpointer checkpointerLogger (_pactModuleCacheLimit config) sqlenv (_pactPersistIntraBlockWrites config) ver cid $ \checkpointer -> do
        let !rs = readRewards
        let !pse = PactServiceEnv
                    { _psMempoolAccess = Nothing
                    , _psCheckpointer = checkpointer
                    , _psPdb = pdb
                    , _psBlockHeaderDb = bhDb
                    , _psGasModel = getGasModel
                    , _psMinerRewards = rs
                    , _psReorgLimit = _pactReorgLimit config
                    , _psPreInsertCheckTimeout = _pactPreInsertCheckTimeout config
                    , _psOnFatalError = defaultOnFatalError (logFunctionText chainwebLogger)
                    , _psVersion = ver
                    , _psAllowReadsInLocal = _pactAllowReadsInLocal config
                    , _psLogger = pactServiceLogger
                    , _psGasLogger = gasLogger <$ guard (_pactLogGas config)
                    , _psBlockGasLimit = _pactBlockGasLimit config
                    , _psEnableLocalTimeout = _pactEnableLocalTimeout config
                    , _psTxFailuresCounter = txFailuresCounter
                    }
            !pst = PactServiceState mempty

        when (_pactFullHistoryRequired config) $ do
          mEarliestBlock <- _cpGetEarliestBlock (_cpReadCp checkpointer)
          case mEarliestBlock of
            Nothing -> do
              pure ()
            Just (earliestBlockHeight, _) -> do
              let gHeight = genesisHeight ver cid
              when (gHeight /= earliestBlockHeight) $ do
                let e = FullHistoryRequired
                      { _earliestBlockHeight = earliestBlockHeight
                      , _genesisHeight = gHeight
                      }
                let msg = J.object
                      [ "details" J..= e
                      , "message" J..= J.text "Your node has been configured\
                          \ to require the full Pact history; however, the full\
                          \ history is not available. Perhaps you have compacted\
                          \ your Pact state?"
                      ]
                logError_ chainwebLogger (J.encodeText msg)
                throwM e

        runPactServiceM pst pse $ do
            -- If the latest header that is stored in the checkpointer was on an
            -- orphaned fork, there is no way to recover it in the call of
            -- 'initalPayloadState.readContracts'. We therefore rewind to the latest
            -- avaliable header in the block header database.
            --
            exitOnRewindLimitExceeded $ initializeLatestBlock (_pactUnlimitedInitialRewind config)
            act
  where
    pactServiceLogger = setComponent "pact" chainwebLogger
    checkpointerLogger = addLabel ("sub-component", "checkpointer") pactServiceLogger
    gasLogger = addLabel ("transaction", "GasLogs") pactServiceLogger

initializeLatestBlock :: (Logger logger) => CanReadablePayloadCas tbl => Bool -> PactServiceM logger tbl ()
initializeLatestBlock unlimitedRewind = findLatestValidBlockHeader' >>= \case
    Nothing -> return ()
    Just b -> rewindToIncremental initialRewindLimit (ParentHeader b)
  where
    initialRewindLimit = RewindLimit 1000 <$ guard (not unlimitedRewind)

initialPayloadState
    :: Logger logger
    => CanReadablePayloadCas tbl
    => ChainwebVersion
    -> ChainId
    -> PactServiceM logger tbl ()
initialPayloadState v cid
    | v ^. versionCheats . disablePact = pure ()
    | otherwise = initializeCoinContract v cid $
        v ^?! versionGenesis . genesisBlockPayload . onChain cid

initializeCoinContract
    :: forall tbl logger. (CanReadablePayloadCas tbl, Logger logger)
    => ChainwebVersion
    -> ChainId
    -> PayloadWithOutputs
    -> PactServiceM logger tbl ()
initializeCoinContract v cid pwo = do
    cp <- view psCheckpointer
    latestBlock <- liftIO (_cpGetLatestBlock $ _cpReadCp cp) >>= \case
        Nothing -> return Nothing
        Just (_, latestHash) -> do
            latestHeader <- ParentHeader
                <$!> lookupBlockHeader latestHash "initializeCoinContract.findLatestValidBlockHeader"
            return $ Just latestHeader

    case latestBlock of
      Nothing -> do
        logWarn "initializeCoinContract: Checkpointer returned no latest block. Starting from genesis."
        validateGenesis
      Just currentBlockHeader -> do
        if
          _parentHeader currentBlockHeader /= genesisHeader &&
          not (pact5 v cid $ _blockHeight (_parentHeader currentBlockHeader))
        then do
          !mc <- readFrom (Just currentBlockHeader) (assertBlockPact4 Pact4.readInitModules) >>= \case
            NoHistory -> throwM $ BlockHeaderLookupFailure
              $ "initializeCoinContract: internal error: latest block not found: " <> sshow currentBlockHeader
            Historical mc -> return mc
          updateInitCache mc currentBlockHeader
        else do
          logWarn "initializeCoinContract: Starting from genesis."
          validateGenesis
  where
    validateGenesis = void $!
        execValidateBlock mempty genesisHeader (CheckablePayloadWithOutputs pwo)

    genesisHeader :: BlockHeader
    genesisHeader = genesisBlockHeader v cid

-- | Lookup a block header.
--
-- The block header is expected to be either in the block header database or to
-- be the the currently stored '_psParentHeader'. The latter addresses the case
-- when a block has already been validate with 'execValidateBlock' but isn't (yet)
-- available in the block header database. If that's the case two things can
-- happen:
--
-- 1. the header becomes available before the next 'execValidateBlock' call, or
-- 2. the header gets orphaned and the next 'execValidateBlock' call would cause
--    a rewind to an ancestor, which is available in the db.
--
lookupBlockHeader :: BlockHash -> Text -> PactServiceM logger tbl BlockHeader
lookupBlockHeader bhash ctx = do
    bhdb <- view psBlockHeaderDb
    liftIO $! lookupM bhdb bhash `catchAllSynchronous` \e ->
        throwM $ BlockHeaderLookupFailure $
            "failed lookup of parent header in " <> ctx <> ": " <> sshow e

-- | Loop forever, serving Pact execution requests and reponses from the queues
serviceRequests
    :: forall logger tbl. (Logger logger, CanReadablePayloadCas tbl)
    => MemPoolAccess
    -> PactQueue
    -> PactServiceM logger tbl ()
serviceRequests memPoolAccess reqQ = go
  where
    go :: PactServiceM logger tbl ()
    go = do
        PactServiceEnv{_psLogger} <- ask
        logDebug "serviceRequests: wait"
        SubmittedRequestMsg msg statusRef <- liftIO $ getNextRequest reqQ
        requestId <- liftIO $ UUID.toText <$> UUID.nextRandom
        let
          logFn :: LogFunction
          logFn = logFunction $ addLabel ("pact-request-id", requestId) _psLogger
        logDebug $ "serviceRequests: " <> sshow msg
        case msg of
            CloseMsg ->
                tryOne "execClose" statusRef $ return ()
            LocalMsg (LocalReq localRequest preflight sigVerify rewindDepth) -> do
                trace logFn "Chainweb.Pact.PactService.execLocal" () 0 $
                    tryOne "execLocal" statusRef $
                        execLocal localRequest preflight sigVerify rewindDepth
                go
            NewBlockMsg NewBlockReq {..} -> do
                trace logFn "Chainweb.Pact.PactService.execNewBlock"
                    () 1 $
                    tryOne "execNewBlock" statusRef $
                        execNewBlock memPoolAccess _newBlockMiner _newBlockFill _newBlockParent
                go
            ContinueBlockMsg (ContinueBlockReq bip) -> do
                trace logFn "Chainweb.Pact.PactService.execContinueBlock"
                    () 1 $
                    tryOne "execContinueBlock" statusRef $
                        execContinueBlock memPoolAccess bip
                go
            ValidateBlockMsg ValidateBlockReq {..} -> do
                tryOne "execValidateBlock" statusRef $
                  fmap fst $ trace' logFn "Chainweb.Pact.PactService.execValidateBlock"
                    _valBlockHeader
                    (\(_, g) -> fromIntegral g)
                    (execValidateBlock memPoolAccess _valBlockHeader _valCheckablePayload)
                go
            LookupPactTxsMsg (LookupPactTxsReq confDepth txHashes) -> do
                trace logFn "Chainweb.Pact.PactService.execLookupPactTxs" ()
                    (length txHashes) $
                    tryOne "execLookupPactTxs" statusRef $
                        execLookupPactTxs confDepth txHashes
                go
            PreInsertCheckMsg (PreInsertCheckReq txs) -> do
                trace logFn "Chainweb.Pact.PactService.execPreInsertCheckReq" ()
                    (length txs) $
                    tryOne "execPreInsertCheckReq" statusRef $
                        V.map (() <$) <$> execPreInsertCheckReq txs
                go
            BlockTxHistoryMsg (BlockTxHistoryReq bh d) -> do
                trace logFn "Chainweb.Pact.PactService.execBlockTxHistory" bh 1 $
                    tryOne "execBlockTxHistory" statusRef $
                        execBlockTxHistory bh d
                go
            HistoricalLookupMsg (HistoricalLookupReq bh d k) -> do
                trace logFn "Chainweb.Pact.PactService.execHistoricalLookup" bh 1 $
                    tryOne "execHistoricalLookup" statusRef $
                        execHistoricalLookup bh d k
                go
            SyncToBlockMsg SyncToBlockReq {..} -> do
                trace logFn "Chainweb.Pact.PactService.execSyncToBlock" _syncToBlockHeader 1 $
                    tryOne "syncToBlockBlock" statusRef $
                        execSyncToBlock _syncToBlockHeader
                go
            ReadOnlyReplayMsg ReadOnlyReplayReq {..} -> do
                trace logFn "Chainweb.Pact.PactService.execReadOnlyReplay" (_readOnlyReplayLowerBound, _readOnlyReplayUpperBound) 1 $
                    tryOne "readOnlyReplayBlock" statusRef $
                        execReadOnlyReplay _readOnlyReplayLowerBound _readOnlyReplayUpperBound
                go

    tryOne
        :: forall a. Text
        -> TVar (RequestStatus a)
        -> PactServiceM logger tbl a
        -> PactServiceM logger tbl ()
    tryOne which statusRef act =
        evalPactOnThread
        `catches`
            [ Handler $ \(e :: SomeException) -> do
                logError $ mconcat
                    [ "Received exception running pact service ("
                    , which
                    , "): "
                    , sshow e
                    ]
                liftIO $ throwIO e
           ]
      where
        -- here we start a thread to service the request
        evalPactOnThread :: PactServiceM logger tbl ()
        evalPactOnThread = do
            maybeException <- withPactState $ \run -> do
                goLock <- newEmptyMVar
                finishedLock <- newEmptyMVar
                -- fork a thread to service the request
                bracket
                    (forkIO $
                        -- We wrap this whole block in `tryAsync` because we
                        -- want to ignore `RequestCancelled` exceptions that
                        -- occur while we are waiting on `takeMVar goLock`.
                        --
                        -- Otherwise we get logs like `chainweb-node:
                        -- RequestCancelled`.
                        --
                        -- We don't actually care about whether or not
                        -- `RequestCancelled` was encountered, so we just `void`
                        -- it.
                        void $ tryAsync @_ @RequestCancelled $ flip finally (tryPutMVar finishedLock ()) $ do
                            -- wait until we've been told to start.
                            -- we don't want to start if the request was cancelled
                            -- already
                            takeMVar goLock

                            -- run and report the answer.
                            tryAny (run act) >>= \case
                                Left ex -> atomically $ writeTVar statusRef (RequestFailed ex)
                                Right r -> atomically $ writeTVar statusRef (RequestDone r)
                    )
                    -- if Pact itself is killed, kill the request thread too.
                    (\tid -> throwTo tid RequestCancelled >> takeMVar finishedLock)
                    (\_tid -> do
                        -- check first if the request has been cancelled before
                        -- starting work on it
                        beforeStarting <- atomically $ do
                            readTVar statusRef >>= \case
                                RequestInProgress ->
                                    error "PactService internal error: request in progress before starting"
                                RequestDone _ ->
                                    error "PactService internal error: request finished before starting"
                                RequestFailed e ->
                                    return (Left e)
                                RequestNotStarted -> do
                                    writeTVar statusRef RequestInProgress
                                    return (Right ())
                        case beforeStarting of
                            -- the request has already been cancelled, don't
                            -- start work on it.
                            Left ex -> return (Left ex)
                            Right () -> do
                                -- let the request thread start working
                                putMVar goLock ()
                                -- wait until the request thread has finished
                                atomically $ readTVar statusRef >>= \case
                                    RequestInProgress -> retry
                                    RequestDone _ -> return (Right ())
                                    RequestFailed e -> return (Left e)
                                    RequestNotStarted -> error "PactService internal error: request not started after starting"
                    )
            case maybeException of
              Left (fromException -> Just AsyncCancelled) -> do
                liftIO $ putStrLn "Pact action was cancelled"
                logDebug "Pact action was cancelled"
              Left (fromException -> Just ThreadKilled) -> do
                liftIO $ putStrLn "Pact action thread was killed"
                logWarn "Pact action thread was killed"
              Left (exn :: SomeException) -> do
                liftIO $ putStrLn $ "Exception " ++ sshow exn
                logError $ mconcat
                  [ "Received exception running pact service ("
                  , which
                  , "): "
                  , sshow exn
                  ]
              Right () -> return ()

execNewBlock
  :: forall logger tbl. (Logger logger, CanReadablePayloadCas tbl)
  => MemPoolAccess
  -> Miner
  -> NewBlockFill
  -> ParentHeader
  -> PactServiceM logger tbl (Historical (ForSomePactVersion BlockInProgress))
execNewBlock mpAccess miner fill newBlockParent = pactLabel "execNewBlock" $ do
    readFrom (Just newBlockParent) $ do
      blockDbEnv <- view psBlockDbEnv
      pactDb <- liftIO $ assertDynamicPact4Db (_cpPactDbEnv blockDbEnv)
      let pHeight = _blockHeight $ _parentHeader newBlockParent
      let pHash = _blockHash $ _parentHeader newBlockParent
      liftPactServiceM $
          logInfo $ "(parent height = " <> sshow pHeight <> ")"
                <> " (parent hash = " <> sshow pHash <> ")"
      blockGasLimit <- view (psServiceEnv . psBlockGasLimit)
      if pact5 v cid (succ pHeight) then do
        assertBlockPact5 $ do
          undefined
      else assertBlockPact4 $ do
        initCache <- initModuleCacheForBlock False
        coinbaseOutput <- runPact4Coinbase False miner (EnforceCoinbaseFailure True) (CoinbaseUsePrecompiled True) initCache
        finalBlockState <- fmap _benvBlockState
          $ liftIO
          $ readMVar
          $ pdPactDbVar
          $ pactDb
        let blockInProgress = BlockInProgress
                { _blockInProgressModuleCache = Pact4ModuleCache initCache
                -- ^ we do not use the module cache populated by coinbase in
                -- subsequent transactions
                , _blockInProgressPendingData = _bsPendingBlock finalBlockState
                , _blockInProgressTxId = _bsTxId finalBlockState
                , _blockInProgressParentHeader = newBlockParent
                , _blockInProgressRemainingGasLimit = fromIntegral blockGasLimit
                , _blockInProgressTransactions = Transactions
                    { _transactionCoinbase = coinbaseOutput
                    , _transactionPairs = mempty
                    }
                , _blockInProgressMiner = miner
                , _blockInProgressPactVersion = Pact4T
                }
        case fill of
          NewBlockFill -> undefined -- continueBlock mpAccess Pact4T blockInProgress
          NewBlockEmpty -> return (ForPact4 blockInProgress)
    where
    v = _chainwebVersion newBlockParent
    cid = _chainId newBlockParent

execContinueBlock
    :: forall logger tbl pv. (Logger logger, CanReadablePayloadCas tbl)
    => MemPoolAccess
    -> BlockInProgress pv
    -> PactServiceM logger tbl (Historical (BlockInProgress pv))
execContinueBlock mpAccess blockInProgress = pactLabel "execNewBlock" $ do
    readFrom (Just newBlockParent) $
      case _blockInProgressPactVersion blockInProgress of
        Pact4T -> assertBlockPact4 $ Pact4.continueBlock mpAccess blockInProgress
        Pact5T -> undefined
    where
    newBlockParent = _blockInProgressParentHeader blockInProgress


-- | only for use in generating genesis blocks in tools.
--   only supports Pact 4.
--
execNewGenesisBlock
    :: (Logger logger, CanReadablePayloadCas tbl)
    => Miner
    -> Vector Pact4.Transaction
    -> PactServiceM logger tbl PayloadWithOutputs
execNewGenesisBlock miner newTrans = pactLabel "execNewGenesisBlock" $ do
    historicalBlock <- readFrom Nothing $ do
      -- NEW GENESIS COINBASE: Reject bad coinbase, use date rule for precompilation
      results <- assertBlockPact4 $
        execTransactions True miner newTrans
          (EnforceCoinbaseFailure True)
          (CoinbaseUsePrecompiled False) Nothing Nothing
          >>= throwCommandInvalidError
      return $! toPayloadWithOutputs Pact4T miner results
    case historicalBlock of
      NoHistory -> internalError "PactService.execNewGenesisBlock: Impossible error, unable to rewind before genesis"
      Historical block -> return block

execReadOnlyReplay
    :: forall logger tbl
    . (Logger logger, CanReadablePayloadCas tbl)
    => BlockHeader
    -> Maybe BlockHeader
    -> PactServiceM logger tbl ()
execReadOnlyReplay lowerBound maybeUpperBound = pactLabel "execReadOnlyReplay" $ do
    ParentHeader cur <- findLatestValidBlockHeader
    logger <- view psLogger
    bhdb <- view psBlockHeaderDb
    pdb <- view psPdb
    v <- view chainwebVersion
    cid <- view chainId
    -- lower bound must be an ancestor of upper.
    upperBound <- case maybeUpperBound of
        Just upperBound -> do
            liftIO (ancestorOf bhdb (_blockHash lowerBound) (_blockHash upperBound)) >>=
                flip unless (internalError "lower bound is not an ancestor of upper bound")

            -- upper bound must be an ancestor of latest header.
            liftIO (ancestorOf bhdb (_blockHash upperBound) (_blockHash cur)) >>=
                flip unless (internalError "upper bound is not an ancestor of latest header")

            return upperBound
        Nothing -> do
            liftIO (ancestorOf bhdb (_blockHash lowerBound) (_blockHash cur)) >>=
                flip unless (internalError "lower bound is not an ancestor of latest header")

            return cur
    liftIO $ logFunctionText logger Info $ "pact db replaying between blocks "
        <> sshow (_blockHeight lowerBound, _blockHash lowerBound) <> " and "
        <> sshow (_blockHeight upperBound, _blockHash upperBound)

    let genHeight = genesisHeight v cid
    -- we don't want to replay the genesis header in here.
    let lowerHeight = max (succ genHeight) (_blockHeight lowerBound)
    withPactState $ \runPact ->
        liftIO $ getBranchIncreasing bhdb upperBound (int lowerHeight) $ \blocks -> do
          heightRef <- newIORef lowerHeight
          withAsync (heightProgress lowerHeight heightRef (logInfo_ logger)) $ \_ -> do
              blocks
                  & Stream.hoist liftIO
                  & play bhdb pdb heightRef runPact
    where

    play
      :: CanReadablePayloadCas tbl
      => BlockHeaderDb
      -> PayloadDb tbl
      -> IORef BlockHeight
      -> (forall a. PactServiceM logger tbl a -> IO a)
      -> Stream.Stream (Stream.Of BlockHeader) IO r
      -> IO r
    play bhdb pdb heightRef runPact blocks = do
        logger <- runPact $ view psLogger
        validationFailedRef <- newIORef False
        r <- blocks & Stream.mapM_ (\bh -> do
            bhParent <- liftIO $ lookupParentM GenesisParentThrow bhdb bh
            let
                printValidationError (BlockValidationFailure (BlockValidationFailureMsg m)) = do
                    writeIORef validationFailedRef True
                    logFunctionText logger Error (J.getJsonText m)
                printValidationError e = throwM e
                handleMissingBlock NoHistory = throwM $ BlockHeaderLookupFailure $
                  "execReadOnlyReplay: missing block: " <> sshow bh
                handleMissingBlock (Historical ()) = return ()
            handle printValidationError
                $ (handleMissingBlock =<<)
                $ runPact
                $ readFrom (Just $ ParentHeader bhParent) $ do
                    liftIO $ writeIORef heightRef (_blockHeight bh)
                    payload <- liftIO $ fromJuste <$>
                      lookupPayloadDataWithHeight pdb (Just $ _blockHeight bh) (_blockPayloadHash bh)
                    void $ assertBlockPact4 $ Pact4.execBlock bh (CheckablePayload payload)
            )
        validationFailed <- readIORef validationFailedRef
        when validationFailed $
            throwM $ BlockValidationFailure $ BlockValidationFailureMsg $
              J.encodeJsonText ("Prior block validation errors" :: Text)
        return r

    heightProgress :: BlockHeight -> IORef BlockHeight -> (Text -> IO ()) -> IO ()
    heightProgress initialHeight ref logFun = do
        r <- newIORef initialHeight
        let delaySecs = 20
        forever $ do
          h <- readIORef r
          h' <- readIORef ref
          writeIORef r h'
          logFun
            $ "processed: " <> sshow (h' - initialHeight)
            <> ", current height: " <> sshow h'
            <> ", rate: " <> sshow ((h' - h) `div` fromIntegral delaySecs) <> "blocks/sec"
          liftIO $ threadDelay (delaySecs * 1_000_000)

execLocal
    :: (Logger logger, CanReadablePayloadCas tbl)
    => Pact4.Transaction
    -> Maybe LocalPreflightSimulation
      -- ^ preflight flag
    -> Maybe LocalSignatureVerification
      -- ^ turn off signature verification checks?
    -> Maybe RewindDepth
      -- ^ rewind depth
    -> PactServiceM logger tbl LocalResult
execLocal cwtx preflight sigVerify rdepth = pactLabel "execLocal" $ do

    PactServiceEnv{..} <- ask

    let !cmd = Pact4.payloadObj <$> cwtx
        !pm = Pact4.publicMetaOf cmd

    bhdb <- view psBlockHeaderDb

    -- when no depth is defined, treat
    -- withCheckpointerRewind as readFrom
    -- (i.e. setting rewind to 0).
    let rewindDepth = maybe 0 _rewindDepth rdepth

    let timeoutLimit
          | _psEnableLocalTimeout = Just (2 * 1_000_000)
          | otherwise = Nothing

    let act = readFromNthParent (fromIntegral rewindDepth) $ do
                pc <- view psParentHeader
                let spv = pactSPV bhdb (_parentHeader pc)
                ctx <- getTxContext noMiner pm
                let gasModel = getGasModel ctx
                mc <- getInitCache
                dbEnv <- liftIO . assertDynamicPact4Db . _cpPactDbEnv =<< view psBlockDbEnv

                --
                -- if the ?preflight query parameter is set to True, we run the `applyCmd` workflow
                -- otherwise, we prefer the old (default) behavior. When no preflight flag is
                -- specified, we run the old behavior. When it is set to true, we also do metadata
                -- validations.
                --
                case preflight of
                  Just PreflightSimulation -> do
                    liftPactServiceM (Pact4.assertLocalMetadata cmd ctx sigVerify) >>= \case
                      Right{} -> do
                        let initialGas = Pact4.initialGasOf $ P._cmdPayload cwtx
                        T3 cr _mc warns <- liftIO $ Pact4.applyCmd
                          _psVersion _psLogger _psGasLogger Nothing dbEnv
                          noMiner gasModel ctx spv cmd
                          initialGas mc ApplyLocal

                        let cr' = toHashCommandResult cr
                            warns' = P.renderCompactText <$> toList warns
                        pure $ LocalResultWithWarns cr' warns'
                      Left e -> pure $ MetadataValidationFailure e
                  _ -> liftIO $ do
                    let execConfig = P.mkExecutionConfig $
                            [ P.FlagAllowReadInLocal | _psAllowReadsInLocal ] ++
                            Pact4.enablePactEvents' (_chainwebVersion ctx) (_chainId ctx) (ctxCurrentBlockHeight ctx) ++
                            Pact4.enforceKeysetFormats' (_chainwebVersion ctx) (_chainId ctx) (ctxCurrentBlockHeight ctx) ++
                            Pact4.disableReturnRTC (_chainwebVersion ctx) (_chainId ctx) (ctxCurrentBlockHeight ctx)

                    cr <- Pact4.applyLocal
                      _psLogger _psGasLogger dbEnv
                      gasModel  ctx spv
                      cwtx mc execConfig

                    let cr' = toHashCommandResult cr
                    pure $ LocalResultLegacy cr'

    case timeoutLimit of
      Nothing -> act
      Just limit -> withPactState $ \run -> timeoutYield limit (run act) >>= \case
        Just r -> pure r
        Nothing -> do
          logError_ _psLogger $ "Local action timed out for cwtx:\n" <> sshow cwtx
          pure LocalTimeout

execSyncToBlock
    :: (CanReadablePayloadCas tbl, Logger logger)
    => BlockHeader
    -> PactServiceM logger tbl ()
execSyncToBlock targetHeader = pactLabel "execSyncToBlock" $ do
  latestHeader <- findLatestValidBlockHeader' >>= maybe failNonGenesisOnEmptyDb return
  if latestHeader == targetHeader
  then do
      logInfo $ "checkpointer at checkpointer target"
          <> ". target height: " <> sshow (_blockHeight latestHeader)
          <> "; target hash: " <> blockHashToText (_blockHash latestHeader)
  else do
      logInfo $ "rewind to checkpointer target"
          <> ". current height: " <> sshow (_blockHeight latestHeader)
          <> "; current hash: " <> blockHashToText (_blockHash latestHeader)
          <> "; target height: " <> sshow targetHeight
          <> "; target hash: " <> blockHashToText targetHash
  rewindToIncremental Nothing (ParentHeader targetHeader)
  where
  targetHeight = _blockHeight targetHeader
  targetHash = _blockHash targetHeader
  failNonGenesisOnEmptyDb = error "impossible: playing non-genesis block to empty DB"

-- | Validate a mined block `(headerToValidate, payloadToValidate).
-- Note: The BlockHeader here is the header of the block being validated.
-- To do this, we atomically:
-- - determine if the block is on a different fork from the checkpointer's
--   current latest block, and execute all of the blocks on that fork if so,
--   all the way to the parent of the block we're validating.
-- - run the Pact transactions in the block.
-- - commit the result to the database.
--
execValidateBlock
    :: (CanReadablePayloadCas tbl, Logger logger)
    => MemPoolAccess
    -> BlockHeader
    -> CheckablePayload
    -> PactServiceM logger tbl (PayloadWithOutputs, P.Gas)
execValidateBlock memPoolAccess headerToValidate payloadToValidate = pactLabel "execValidateBlock" $ do
    bhdb <- view psBlockHeaderDb
    payloadDb <- view psPdb
    v <- view chainwebVersion
    cid <- view chainId
    RewindLimit reorgLimit <- view psReorgLimit

    -- The parent block header must be available in the block header database.
    parentOfHeaderToValidate <- getTarget

    -- Add block-hash to the logs if presented
    let logBlockHash =
            localLabel ("block-hash", blockHashToText (_blockParent headerToValidate))

    logBlockHash $ do
        currHeader <- findLatestValidBlockHeader'
        -- find the common ancestor of the new block and our current block
        commonAncestor <- liftIO $ case (currHeader, parentOfHeaderToValidate) of
            (Just currHeader', Just ph) ->
                Just <$> forkEntry bhdb currHeader' (_parentHeader ph)
            _ ->
                return Nothing
        -- check that we don't exceed the rewind limit. for the purpose
        -- of this check, the genesis block and the genesis parent
        -- have the same height.
        let !currHeight = maybe (genesisHeight v cid) _blockHeight currHeader
        let !ancestorHeight = maybe (genesisHeight v cid) _blockHeight commonAncestor
        let !rewindLimitSatisfied = ancestorHeight + fromIntegral reorgLimit >= currHeight
        unless rewindLimitSatisfied $
            throwM $ RewindLimitExceeded
                (RewindLimit reorgLimit)
                currHeader
                commonAncestor
        -- get all blocks on the fork we're going to play, up to the parent
        -- of the block we're validating
        let withForkBlockStream kont = case parentOfHeaderToValidate of
                Nothing ->
                    -- we're validating a genesis block, so there are no fork blocks to speak of.
                    kont (pure ())
                Just (ParentHeader parentHeaderOfHeaderToValidate) ->
                    let forkStartHeight = maybe (genesisHeight v cid) (succ . _blockHeight) commonAncestor
                    in getBranchIncreasing bhdb parentHeaderOfHeaderToValidate (fromIntegral forkStartHeight) kont

        ((), results) <-
            withPactState $ \runPact ->
                withForkBlockStream $ \forkBlockHeaders -> do

                    -- given a header for a block in the fork, fetch its payload
                    -- and run its transactions, validating its hashes
                    let runForkBlockHeaders = Stream.map (\forkBh -> do
                            payload <- liftIO $ lookupPayloadWithHeight payloadDb (Just $ _blockHeight forkBh) (_blockPayloadHash forkBh) >>= \case
                                Nothing -> internalError
                                    $ "execValidateBlock: lookup of payload failed"
                                    <> ". BlockPayloadHash: " <> encodeToText (_blockPayloadHash forkBh)
                                    <> ". Block: " <> encodeToText (ObjectEncoded forkBh)
                                Just x -> return $ payloadWithOutputsToPayloadData x
                            void $ assertBlockPact4 $ Pact4.execBlock forkBh (CheckablePayload payload)
                            return ([], forkBh)
                            ) forkBlockHeaders

                    -- run the new block, the one we're validating, and
                    -- validate its hashes
                    let runThisBlock = Stream.yield $ do
                            !output <- assertBlockPact4 $ Pact4.execBlock headerToValidate payloadToValidate
                            return ([output], headerToValidate)

                    -- here we rewind to the common ancestor block, run the
                    -- transactions in all of its child blocks until the parent
                    -- of the block we're validating, then run the block we're
                    -- validating.
                    runPact $ restoreAndSave
                        (ParentHeader <$> commonAncestor)
                        (runForkBlockHeaders >> runThisBlock)
        let logRewind =
                -- we consider a fork of height more than 3 to be notable.
                if ancestorHeight + 3 < currHeight
                then logWarn
                else logDebug
        logRewind $
            "execValidateBlock: rewound " <> sshow (currHeight - ancestorHeight) <> " blocks"
        (totalGasUsed, result) <- case results of
            [r] -> return r
            _ -> internalError "execValidateBlock: wrong number of block results returned from _cpRestoreAndSave."

        -- update mempool
        --
        -- Using the parent isn't optimal, since it doesn't delete the txs of
        -- `currHeader` from the set of pending tx. The reason for this is that the
        -- implementation 'mpaProcessFork' uses the chain database and at this point
        -- 'currHeader' is generally not yet available in the database. It would be
        -- possible to extract the txs from the result and remove them from the set
        -- of pending txs. However, that would add extra complexity and at little
        -- gain.
        --
        case parentOfHeaderToValidate of
            Nothing -> return ()
            Just (ParentHeader p) -> liftIO $ do
                mpaProcessFork memPoolAccess p
                mpaSetLastHeader memPoolAccess p

        return (result, totalGasUsed)

  where
    getTarget
        | isGenesisBlockHeader headerToValidate = return Nothing
        | otherwise = Just . ParentHeader
            <$> lookupBlockHeader (_blockParent headerToValidate) "execValidateBlock"
                -- It is up to the user of pact service to guaranteed that this
                -- succeeds. If this fails it usually means that the block
                -- header database is corrupted.

execBlockTxHistory
    :: Logger logger
    => BlockHeader
    -> P.Domain P.RowKey P.RowData
    -> PactServiceM logger tbl (Historical BlockTxHistory)
execBlockTxHistory bh d = pactLabel "execBlockTxHistory" $ do
  !cp <- view psCheckpointer
  liftIO $ _cpGetBlockHistory (_cpReadCp cp) bh d

execHistoricalLookup
    :: Logger logger
    => BlockHeader
    -> P.Domain P.RowKey P.RowData
    -> P.RowKey
    -> PactServiceM logger tbl (Historical (Maybe (Pact5.TxLog Pact5.RowData)))
execHistoricalLookup bh d k = pactLabel "execHistoricalLookup" $ do
  !cp <- view psCheckpointer
  liftIO $ _cpGetHistoricalLookup (_cpReadCp cp) bh d k

execPreInsertCheckReq
    :: (CanReadablePayloadCas tbl, Logger logger)
    => Vector Pact4.Transaction
    -> PactServiceM logger tbl (Vector (Either Mempool.InsertError Pact4.Transaction))
execPreInsertCheckReq txs = pactLabel "execPreInsertCheckReq" $ do
    let requestKeys = V.map P.cmdToRequestKey txs
    logInfo $ "(request keys = " <> sshow requestKeys <> ")"
    psEnv <- ask
    psState <- get
    logger <- view psLogger
    let timeoutLimit = fromIntegral $ (\(Micros n) -> n) $ _psPreInsertCheckTimeout psEnv
    let act =
          readFromLatest $ do
            pdb <- view psBlockDbEnv
            db' <- traverseOf cpPactDbEnv assertDynamicPact4Db pdb
            pc <- view psParentHeader
            let
                parentTime = ParentCreationTime (_blockCreationTime $ _parentHeader pc)
                currHeight = succ $ _blockHeight $ _parentHeader pc
                v = _chainwebVersion pc
                cid = _chainId pc
            liftIO $ Pact4.validateChainwebTxs logger v cid db' parentTime currHeight txs
              (evalPactServiceM psState psEnv . runPactBlockM pc pdb . attemptBuyGas noMiner)
    withPactState $ \run ->
      timeoutYield timeoutLimit (run act) >>= \case
        Just r -> pure r
        Nothing -> do
          logError_ logger $ "Mempool pre-insert check timed out for txs:\n" <> sshow txs
          pure $ V.map (const $ Left Mempool.InsertErrorTimedOut) txs

  where
    attemptBuyGas
        :: forall logger tbl. (Logger logger)
        => Miner
        -> Vector (Either InsertError Pact4.Transaction)
        -> PactBlockM logger (DynamicPactDb logger) tbl (Vector (Either InsertError Pact4.Transaction))
    attemptBuyGas miner txsOrErrs = localLabelBlock ("transaction", "attemptBuyGas") $ do
            mc <- getInitCache
            l <- view (psServiceEnv . psLogger)
            V.fromList . toList . sfst <$> V.foldM (buyGasFor l) (T2 mempty mc) txsOrErrs
      where
        buyGasFor :: logger
          -> T2 (DL.DList (Either InsertError Pact4.Transaction)) ModuleCache
          -> Either InsertError Pact4.Transaction
          -> PactBlockM logger (DynamicPactDb logger) tbl (T2 (DL.DList (Either InsertError Pact4.Transaction)) ModuleCache)
        buyGasFor _l (T2 dl mcache) err@Left {} = return (T2 (DL.snoc dl err) mcache)
        buyGasFor l (T2 dl mcache) (Right tx) = do
            T2 mcache' !res <- do
              let cmd = Pact4.payloadObj <$> tx
                  gasPrice = view Pact4.cmdGasPrice cmd
                  gasLimit = fromIntegral $ view Pact4.cmdGasLimit cmd
                  txst = Pact4.TransactionState
                      { _txCache = mcache
                      , _txLogs = mempty
                      , _txGasUsed = 0
                      , _txGasId = Nothing
                      , _txGasModel = P._geGasModel P.freeGasEnv
                      , _txWarnings = mempty
                      }
              let !nid = Pact4.networkIdOf cmd
              let !rk = P.cmdToRequestKey cmd
              pd <- getTxContext miner (Pact4.publicMetaOf cmd)
              bhdb <- view (psServiceEnv . psBlockHeaderDb)
              dbEnv <- liftIO . assertDynamicPact4Db . _cpPactDbEnv =<< view psBlockDbEnv
              spv <- pactSPV bhdb . _parentHeader <$> view psParentHeader
              let ec = P.mkExecutionConfig $
                    [ P.FlagDisableModuleInstall
                    , P.FlagDisableHistoryInTransactionalMode ] ++
                    Pact4.disableReturnRTC (ctxVersion pd) (ctxChainId pd) (ctxCurrentBlockHeight pd)
              -- TODO: use Pact5's buygas here
              let buyGasEnv = Pact4.TransactionEnv P.Transactional dbEnv l Nothing (ctxToPublicData pd) spv nid gasPrice rk gasLimit ec Nothing Nothing

              cr <- liftIO
                $! catchesPact4Error l CensorsUnexpectedError
                $! Pact4.execTransactionM buyGasEnv txst
                $! Pact4.buyGas pd cmd miner

              case cr of
                  Left err -> return (T2 mcache (Left (InsertErrorBuyGas (T.pack $ show err))))
                  Right t -> return (T2 (Pact4._txCache t) (Right tx))
            pure $! T2 (DL.snoc dl res) mcache'

execLookupPactTxs
    :: (CanReadablePayloadCas tbl, Logger logger)
    => Maybe ConfirmationDepth
    -> Vector P.PactHash
    -> PactServiceM logger tbl (HM.HashMap P.PactHash (T2 BlockHeight BlockHash))
execLookupPactTxs confDepth txs = pactLabel "execLookupPactTxs" $ do
  if V.null txs then return mempty else go
  where
    go = readFromNthParent (maybe 0 (fromIntegral . _confirmationDepth) confDepth) $ do
      dbenv <- view psBlockDbEnv
      liftIO $ _cpLookupProcessedTx dbenv txs

-- | Modified table gas module with free module loads
--
freeModuleLoadGasModel :: P.GasModel
freeModuleLoadGasModel = modifiedGasModel
  where
    defGasModel = tableGasModel defaultGasConfig
    fullRunFunction = P.runGasModel defGasModel
    modifiedRunFunction name ga = case ga of
      P.GPostRead P.ReadModule {} -> P.MilliGas 0
      _ -> fullRunFunction name ga
    modifiedGasModel = defGasModel { P.runGasModel = modifiedRunFunction }

chainweb213GasModel :: P.GasModel
chainweb213GasModel = modifiedGasModel
  where
    defGasModel = tableGasModel gasConfig
    unknownOperationPenalty = 1000000
    multiRowOperation = 40000
    gasConfig = defaultGasConfig { _gasCostConfig_primTable = updTable }
    updTable = M.union upd defaultGasTable
    upd = M.fromList
      [("keys",    multiRowOperation)
      ,("select",  multiRowOperation)
      ,("fold-db", multiRowOperation)
      ]
    fullRunFunction = P.runGasModel defGasModel
    modifiedRunFunction name ga = case ga of
      P.GPostRead P.ReadModule {} -> 0
      P.GUnreduced _ts -> case M.lookup name updTable of
        Just g -> g
        Nothing -> unknownOperationPenalty
      _ -> P.milliGasToGas $ fullRunFunction name ga
    modifiedGasModel = defGasModel { P.runGasModel = \t g -> P.gasToMilliGas (modifiedRunFunction t g) }

chainweb224GasModel :: P.GasModel
chainweb224GasModel = chainweb213GasModel
  { P.runGasModel = \name -> \case
    P.GPostRead P.ReadInterface {} -> P.MilliGas 0
    ga -> P.runGasModel chainweb213GasModel name ga
  }

getGasModel :: TxContext -> P.GasModel
getGasModel ctx
    | guardCtx chainweb213Pact ctx = chainweb213GasModel
    | guardCtx chainweb224Pact ctx = chainweb224GasModel
    | otherwise = freeModuleLoadGasModel

pactLabel :: (Logger logger) => Text -> PactServiceM logger tbl x -> PactServiceM logger tbl x
pactLabel lbl x = localLabel ("pact-request", lbl) x

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
import Data.Word (Word64)
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
import Chainweb.Pact.PactService.ExecBlock
import Chainweb.Pact.PactService.Checkpointer
import Chainweb.Pact.Service.PactQueue (PactQueue, getNextRequest)
import Chainweb.Pact.Service.Types
import Chainweb.Pact.SPV
import Chainweb.Pact.TransactionExec
import Chainweb.Pact.Types
import Chainweb.Pact.Validations
import Chainweb.Payload
import Chainweb.Payload.PayloadStore
import Chainweb.Time
import Chainweb.Transaction
import Chainweb.TreeDB
import Chainweb.Utils hiding (check)
import Chainweb.Version
import Chainweb.Version.Guards
import Utils.Logging.Trace
import Chainweb.Counter
import Data.Time.Clock
import Text.Printf
import Data.Time.Format.ISO8601

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
        initialPayloadState mempoolAccess ver cid
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
withPactService ver cid chainwebLogger txFailuresCounter bhDb pdb sqlenv config act =
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
    => MemPoolAccess
    -> ChainwebVersion
    -> ChainId
    -> PactServiceM logger tbl ()
initialPayloadState mpa v cid
    | v ^. versionCheats . disablePact = pure ()
    | otherwise = initializeCoinContract mpa v cid $
        v ^?! versionGenesis . genesisBlockPayload . onChain cid

initializeCoinContract
    :: forall tbl logger. (CanReadablePayloadCas tbl, Logger logger)
    => MemPoolAccess
    -> ChainwebVersion
    -> ChainId
    -> PayloadWithOutputs
    -> PactServiceM logger tbl ()
initializeCoinContract memPoolAccess v cid pwo = do
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
        -- We check the block hash because it's more principled and
        -- we don't have to compute it, so the comparison is still relatively
        -- cheap. We could also check the height but that would be redundant.
        if view blockHash (_parentHeader currentBlockHeader) /= view blockHash genesisHeader
        then do
          !mc <- readFrom (Just currentBlockHeader) readInitModules >>= \case
            NoHistory -> throwM $ BlockHeaderLookupFailure
              $ "initializeCoinContract: internal error: latest block not found: " <> sshow currentBlockHeader
            Historical mc -> return mc
          updateInitCache mc currentBlockHeader
        else do
          logWarn "initializeCoinContract: Starting from genesis."
          validateGenesis
  where
    validateGenesis = void $!
        execValidateBlock memPoolAccess genesisHeader (CheckablePayloadWithOutputs pwo)

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
                    (mask_ $ forkIOWithUnmask $ \restore ->
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
                            restore (tryAny (run act)) >>= \case
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
                                RequestInProgress -> internalError "request in progress before starting"
                                RequestDone _ -> internalError "request finished before starting"
                                RequestFailed e -> return (Left e)
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
                                    RequestNotStarted -> internalError "request not started after starting"
                    )
            case maybeException of
              Left (fromException -> Just AsyncCancelled) ->
                logDebug "Pact action was cancelled"
              Left (fromException -> Just ThreadKilled) ->
                logWarn "Pact action thread was killed"
              Left (exn :: SomeException) ->
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
  -> PactServiceM logger tbl (Historical BlockInProgress)
execNewBlock mpAccess miner fill newBlockParent = pactLabel "execNewBlock" $ do
    readFrom (Just newBlockParent) $ do
      blockDbEnv <- view psBlockDbEnv
      let pHeight = view blockHeight $ _parentHeader newBlockParent
      let pHash = view blockHash $ _parentHeader newBlockParent
      liftPactServiceM $
          logInfo $ "(parent height = " <> sshow pHeight <> ")"
                <> " (parent hash = " <> sshow pHash <> ")"
      blockGasLimit <- view (psServiceEnv . psBlockGasLimit)
      initCache <- initModuleCacheForBlock False
      coinbaseOutput <-
          runCoinbase False miner (EnforceCoinbaseFailure True) (CoinbaseUsePrecompiled True) initCache
      finalBlockState <- fmap _benvBlockState
        $ liftIO
        $ readMVar
        $ pdPactDbVar
        $ _cpPactDbEnv blockDbEnv
      let blockInProgress = BlockInProgress
              { _blockInProgressModuleCache = initCache
              -- ^ we do not use the module cache populated by coinbase in
              -- subsequent transactions
              , _blockInProgressPendingData = _bsPendingBlock finalBlockState
              , _blockInProgressTxId = _bsTxId finalBlockState
              , _blockInProgressParentHeader = newBlockParent
              , _blockInProgressRemainingGasLimit = blockGasLimit
              , _blockInProgressTransactions = Transactions
                  { _transactionCoinbase = coinbaseOutput
                  , _transactionPairs = mempty
                  }
              , _blockInProgressMiner = miner
              }
      case fill of
        NewBlockFill -> continueBlock mpAccess blockInProgress
        NewBlockEmpty -> return blockInProgress

execContinueBlock
    :: forall logger tbl. (Logger logger, CanReadablePayloadCas tbl)
    => MemPoolAccess
    -> BlockInProgress
    -> PactServiceM logger tbl (Historical BlockInProgress)
execContinueBlock mpAccess blockInProgress = pactLabel "execNewBlock" $ do
    readFrom (Just newBlockParent) $ continueBlock mpAccess blockInProgress
    where
    newBlockParent = _blockInProgressParentHeader blockInProgress

-- | Note: The ParentHeader param here is the PARENT HEADER of the new
-- block-to-be.
--
continueBlock
    :: forall logger tbl
    . (Logger logger, CanReadablePayloadCas tbl)
    => MemPoolAccess
    -> BlockInProgress
    -> PactBlockM logger tbl BlockInProgress
continueBlock mpAccess blockInProgress = do
    updateMempool
    liftPactServiceM $
      logInfo $ "(parent height = " <> sshow pHeight <> ")"
            <> " (parent hash = " <> sshow pHash <> ")"

    blockDbEnv <- view psBlockDbEnv
    -- restore the block state from the block being continued
    liftIO $
      modifyMVar_ (pdPactDbVar $ _cpPactDbEnv blockDbEnv) $ \blockEnv ->
        return
          $! blockEnv
          & benvBlockState . bsPendingBlock .~ _blockInProgressPendingData blockInProgress
          & benvBlockState . bsTxId .~ _blockInProgressTxId blockInProgress

    blockGasLimit <- view (psServiceEnv . psBlockGasLimit)

    let
        txTimeHeadroomFactor :: Double
        txTimeHeadroomFactor = 5
        -- 2.5 microseconds per unit gas
        txTimeLimit :: Micros
        txTimeLimit = round $ (2.5 * txTimeHeadroomFactor) * fromIntegral blockGasLimit

    let initCache = _blockInProgressModuleCache blockInProgress
    let cb = _transactionCoinbase (_blockInProgressTransactions blockInProgress)
    let startTxs = _transactionPairs (_blockInProgressTransactions blockInProgress)

    successes <- liftIO $ Vec.fromFoldable startTxs
    failures <- liftIO $ Vec.new @_ @_ @TransactionHash

    let initState = BlockFill
          (_blockInProgressRemainingGasLimit blockInProgress)
          (S.fromList $ requestKeyToTransactionHash . P._crReqKey . snd <$> V.toList startTxs)
          0

    -- Heuristic: limit fetches to count of 1000-gas txs in block.
    let fetchLimit = fromIntegral $ blockGasLimit `div` 1000
    T2
      finalModuleCache
      BlockFill { _bfTxHashes = requestKeys, _bfGasLimit = finalGasLimit }
      <- refill fetchLimit txTimeLimit successes failures initCache initState

    liftPactServiceM $ logInfo $ "(request keys = " <> sshow requestKeys <> ")"

    liftIO $ do
      txHashes <- Vec.toLiftedVector failures
      mpaBadlistTx mpAccess txHashes

    txs <- liftIO $ Vec.toLiftedVector successes
    -- edmund: we need to be careful about timeouts.
    -- If a tx times out, it must not be in the block state, otherwise
    -- the "block in progress" will contain pieces of state from that tx.
    --
    -- this cannot happen now because applyPactCmd doesn't let it.
    finalBlockState <- fmap _benvBlockState
      $ liftIO
      $ readMVar
      $ pdPactDbVar
      $ _cpPactDbEnv blockDbEnv
    let !blockInProgress' = BlockInProgress
            { _blockInProgressModuleCache = finalModuleCache
            , _blockInProgressPendingData = _bsPendingBlock finalBlockState
            , _blockInProgressTxId = _bsTxId finalBlockState
            , _blockInProgressParentHeader = newBlockParent
            , _blockInProgressRemainingGasLimit = finalGasLimit
            , _blockInProgressTransactions = Transactions
                { _transactionCoinbase = cb
                , _transactionPairs = txs
                }
            , _blockInProgressMiner = _blockInProgressMiner blockInProgress
            }
    return blockInProgress'
  where
    newBlockParent = _blockInProgressParentHeader blockInProgress

    !parentTime =
      ParentCreationTime (view blockCreationTime $ _parentHeader newBlockParent)

    getBlockTxs :: BlockFill -> PactBlockM logger tbl (Vector ChainwebTransaction)
    getBlockTxs bfState = do
      dbEnv <- view psBlockDbEnv
      psEnv <- ask
      logger <- view (psServiceEnv . psLogger)
      let validate bhi _bha txs = do
            results <- do
                let v = _chainwebVersion psEnv
                    cid = _chainId psEnv
                validateChainwebTxs logger v cid dbEnv parentTime bhi txs return

            V.forM results $ \case
                Right _ -> return True
                Left _e -> return False

      liftIO $!
        mpaGetBlock mpAccess bfState validate (pHeight + 1) pHash (_parentHeader newBlockParent)

    refill
      :: Word64
      -> Micros
      -> GrowableVec (ChainwebTransaction, P.CommandResult [P.TxLogJson])
      -> GrowableVec TransactionHash
      -> ModuleCache -> BlockFill
      -> PactBlockM logger tbl (T2 ModuleCache BlockFill)
    refill fetchLimit txTimeLimit successes failures = go
      where
        go :: ModuleCache -> BlockFill -> PactBlockM logger tbl (T2 ModuleCache BlockFill)
        go mc unchanged@bfState = do

          case unchanged of
            BlockFill g _ c -> do
              (goodLength, badLength) <- liftIO $ (,) <$> Vec.length successes <*> Vec.length failures
              liftPactServiceM $ logDebug $ "Block fill: count=" <> sshow c
                <> ", gaslimit=" <> sshow g <> ", good="
                <> sshow goodLength <> ", bad=" <> sshow badLength

              -- LOOP INVARIANT: limit absolute recursion count
              if _bfCount bfState > fetchLimit then liftPactServiceM $ do
                logInfo $ "Refill fetch limit exceeded (" <> sshow fetchLimit <> ")"
                pure (T2 mc unchanged)
              else do
                when (_bfGasLimit bfState < 0) $
                  throwM $ MempoolFillFailure $ "Internal error, negative gas limit: " <> sshow bfState

                if _bfGasLimit bfState == 0 then pure (T2 mc unchanged) else do

                  newTrans <- getBlockTxs bfState
                  if V.null newTrans then pure (T2 mc unchanged) else do

                    T2 pairs mc' <-
                      execTransactionsOnly
                        (_blockInProgressMiner blockInProgress)
                        newTrans
                        mc
                        (Just txTimeLimit)

                    oldSuccessesLength <- liftIO $ Vec.length successes

                    (newState, timedOut) <- splitResults successes failures unchanged (V.toList pairs)

                    -- LOOP INVARIANT: gas must not increase
                    when (_bfGasLimit newState > _bfGasLimit bfState) $
                      throwM $ MempoolFillFailure $ "Gas must not increase: " <> sshow (bfState,newState)

                    newSuccessesLength <- liftIO $ Vec.length successes
                    let addedSuccessCount = newSuccessesLength - oldSuccessesLength

                    if timedOut
                    then
                      -- a transaction timed out, so give up early and make the block
                      pure (T2 mc' (incCount newState))
                    else if (_bfGasLimit newState >= _bfGasLimit bfState) && addedSuccessCount > 0
                    then
                      -- INVARIANT: gas must decrease if any transactions succeeded
                      throwM $ MempoolFillFailure
                        $ "Invariant failure, gas did not decrease: "
                        <> sshow (bfState,newState,V.length newTrans,addedSuccessCount)
                    else
                      go mc' (incCount newState)

    incCount :: BlockFill -> BlockFill
    incCount b = over bfCount succ b

    -- | Split the results of applying each command into successes and failures,
    --   and return the final 'BlockFill'.
    --
    --   If we encounter a 'TxTimeout', we short-circuit, and only return
    --   what we've put into the block before the timeout. We also report
    --   that we timed out, so that `refill` can stop early.
    --
    --   The failed txs are later badlisted.
    splitResults :: ()
      => GrowableVec (ChainwebTransaction, P.CommandResult [P.TxLogJson])
      -> GrowableVec TransactionHash -- ^ failed txs
      -> BlockFill
      -> [(ChainwebTransaction, Either CommandInvalidError (P.CommandResult [P.TxLogJson]))]
      -> PactBlockM logger tbl (BlockFill, Bool)
    splitResults successes failures = go
      where
        go acc@(BlockFill g rks i) = \case
          [] -> pure (acc, False)
          (t, r) : rest -> case r of
            Right cr -> do
              !rks' <- enforceUnique rks (requestKeyToTransactionHash $ P._crReqKey cr)
              -- Decrement actual gas used from block limit
              let !g' = g - fromIntegral (P._crGas cr)
              liftIO $ Vec.push successes (t, cr)
              go (BlockFill g' rks' i) rest
            Left (CommandInvalidGasPurchaseFailure (GasPurchaseFailure h _)) -> do
              !rks' <- enforceUnique rks h
              -- Gas buy failure adds failed request key to fail list only
              liftIO $ Vec.push failures h
              go (BlockFill g rks' i) rest
            Left (CommandInvalidTxTimeout (TxTimeout h)) -> do
              liftIO $ Vec.push failures h
              liftPactServiceM $ logError $ "timed out on " <> sshow h
              return (acc, True)

    enforceUnique rks rk
      | S.member rk rks =
        throwM $ MempoolFillFailure $ "Duplicate transaction: " <> sshow rk
      | otherwise = return $ S.insert rk rks

    pHeight = view blockHeight $ _parentHeader newBlockParent
    pHash = view blockHash $ _parentHeader newBlockParent

    updateMempool = liftIO $ do
          mpaProcessFork mpAccess $ _parentHeader newBlockParent
          mpaSetLastHeader mpAccess $ _parentHeader newBlockParent

type GrowableVec = Vec (PrimState IO)

-- | only for use in generating genesis blocks in tools
--
execNewGenesisBlock
    :: (Logger logger, CanReadablePayloadCas tbl)
    => Miner
    -> Vector ChainwebTransaction
    -> PactServiceM logger tbl PayloadWithOutputs
execNewGenesisBlock miner newTrans = pactLabel "execNewGenesisBlock" $ do
    historicalBlock <- readFrom Nothing $ do
      -- NEW GENESIS COINBASE: Reject bad coinbase, use date rule for precompilation
      results <- execTransactions True miner newTrans
                 (EnforceCoinbaseFailure True)
                 (CoinbaseUsePrecompiled False) Nothing Nothing
                 >>= throwCommandInvalidError
      return $! toPayloadWithOutputs miner results
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
            liftIO (ancestorOf bhdb (view blockHash lowerBound) (view blockHash upperBound)) >>=
                flip unless (internalError "lower bound is not an ancestor of upper bound")

            -- upper bound must be an ancestor of latest header.
            liftIO (ancestorOf bhdb (view blockHash upperBound) (view blockHash cur)) >>=
                flip unless (internalError "upper bound is not an ancestor of latest header")

            return upperBound
        Nothing -> do
            liftIO (ancestorOf bhdb (view blockHash lowerBound) (view blockHash cur)) >>=
                flip unless (internalError "lower bound is not an ancestor of latest header")

            return cur
    liftIO $ logFunctionText logger Info $ "pact db replaying between blocks "
        <> sshow (view blockHeight lowerBound, view blockHash lowerBound) <> " and "
        <> sshow (view blockHeight upperBound, view blockHash upperBound)

    let genHeight = genesisHeight v cid
    -- we don't want to replay the genesis header in here.
    let lowerHeight = max (succ genHeight) (view blockHeight lowerBound)
    withPactState $ \runPact ->
        liftIO $ getBranchIncreasing bhdb upperBound (int lowerHeight) $ \blocks -> do
          heightRef <- newIORef lowerHeight
          withAsync (heightProgress lowerHeight (view blockHeight upperBound) heightRef (logInfo_ logger)) $ \_ -> do
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
                    logFunctionText logger Error m
                printValidationError e = throwM e
                handleMissingBlock NoHistory = throwM $ BlockHeaderLookupFailure $
                  "execReadOnlyReplay: missing block: " <> sshow bh
                handleMissingBlock (Historical ()) = return ()
            handle printValidationError
                $ (handleMissingBlock =<<)
                $ runPact
                $ readFrom (Just $ ParentHeader bhParent) $ do
                    liftIO $ writeIORef heightRef (view blockHeight bh)
                    payload <- liftIO $ fromJuste <$>
                      lookupPayloadWithHeight pdb (Just $ view blockHeight bh) (view blockPayloadHash bh)
                    let isPayloadEmpty = V.null (_payloadWithOutputsTransactions payload)
                    let isUpgradeBlock = isJust $ _chainwebVersion bhdb ^? versionUpgrades . onChain (_chainId bhdb) . ix (view blockHeight bh)
                    unless (isPayloadEmpty && not isUpgradeBlock) $
                      void $ execBlock bh (CheckablePayloadWithOutputs payload)
            )
        validationFailed <- readIORef validationFailedRef
        when validationFailed $
            throwM $ BlockValidationFailure $ BlockValidationFailureMsg "Prior block validation errors"
        return r

    heightProgress :: BlockHeight -> BlockHeight -> IORef BlockHeight -> (Text -> IO ()) -> IO ()
    heightProgress initialHeight endHeight ref logFun = do
        heightAndRateRef <- newIORef (initialHeight, 0.0 :: Double)
        let delayMicros = 20_000_000
        liftIO $ threadDelay (delayMicros `div` 2)
        forever $ do
          liftIO $ threadDelay delayMicros
          (lastHeight, oldRate) <- readIORef heightAndRateRef
          now' <- getCurrentTime
          currentHeight <- readIORef ref
          let blocksPerSecond
                  = 0.8
                    * oldRate
                  + 0.2
                    * fromIntegral (currentHeight - lastHeight)
                    / (fromIntegral delayMicros / 1_000_000)
          writeIORef heightAndRateRef (currentHeight, blocksPerSecond)
          let est =
                  flip addUTCTime now'
                      $ realToFrac @Double @NominalDiffTime
                      $ fromIntegral @BlockHeight @Double
                          (endHeight - initialHeight)
                      / blocksPerSecond
          logFun
            $ T.pack $ printf "height: %d | rate: %.1f blocks/sec | est. %s"
                      (fromIntegral @BlockHeight @Int $ currentHeight - initialHeight)
                      blocksPerSecond
                      (formatShow iso8601Format est)

execLocal
    :: (Logger logger, CanReadablePayloadCas tbl)
    => ChainwebTransaction
    -> Maybe LocalPreflightSimulation
      -- ^ preflight flag
    -> Maybe LocalSignatureVerification
      -- ^ turn off signature verification checks?
    -> Maybe RewindDepth
      -- ^ rewind depth
    -> PactServiceM logger tbl LocalResult
execLocal cwtx preflight sigVerify rdepth = pactLabel "execLocal" $ do

    PactServiceEnv{..} <- ask

    let !cmd = payloadObj <$> cwtx
        !pm = publicMetaOf cmd

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
                ctx <- getTxContext pm
                let gasModel = getGasModel ctx
                mc <- getInitCache
                dbEnv <- view psBlockDbEnv

                --
                -- if the ?preflight query parameter is set to True, we run the `applyCmd` workflow
                -- otherwise, we prefer the old (default) behavior. When no preflight flag is
                -- specified, we run the old behavior. When it is set to true, we also do metadata
                -- validations.
                --
                case preflight of
                  Just PreflightSimulation -> do
                    liftPactServiceM (assertLocalMetadata cmd ctx sigVerify) >>= \case
                      Right{} -> do
                        let initialGas = initialGasOf $ P._cmdPayload cwtx
                        T3 cr _mc warns <- liftIO $ applyCmd
                          _psVersion _psLogger _psGasLogger Nothing (_cpPactDbEnv dbEnv)
                          noMiner gasModel ctx spv cmd
                          initialGas mc ApplyLocal

                        let cr' = toHashCommandResult cr
                            warns' = P.renderCompactText <$> toList warns
                        pure $ LocalResultWithWarns cr' warns'
                      Left e -> pure $ MetadataValidationFailure e
                  _ -> liftIO $ do
                    let execConfig = P.mkExecutionConfig $
                            [ P.FlagAllowReadInLocal | _psAllowReadsInLocal ] ++
                            enablePactEvents' (_chainwebVersion ctx) (_chainId ctx) (ctxCurrentBlockHeight ctx) ++
                            enforceKeysetFormats' (_chainwebVersion ctx) (_chainId ctx) (ctxCurrentBlockHeight ctx) ++
                            disableReturnRTC (_chainwebVersion ctx) (_chainId ctx) (ctxCurrentBlockHeight ctx)

                    cr <- applyLocal
                      _psLogger _psGasLogger (_cpPactDbEnv dbEnv)
                      gasModel ctx spv
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
          <> ". target height: " <> sshow (view blockHeight latestHeader)
          <> "; target hash: " <> blockHashToText (view blockHash latestHeader)
  else do
      logInfo $ "rewind to checkpointer target"
          <> ". current height: " <> sshow (view blockHeight latestHeader)
          <> "; current hash: " <> blockHashToText (view blockHash latestHeader)
          <> "; target height: " <> sshow targetHeight
          <> "; target hash: " <> blockHashToText targetHash
  rewindToIncremental Nothing (ParentHeader targetHeader)
  where
  targetHeight = view blockHeight targetHeader
  targetHash = view blockHash targetHeader
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
            localLabel ("block-hash", blockHashToText (view blockParent headerToValidate))

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
        let !currHeight = maybe (genesisHeight v cid) (view blockHeight) currHeader
        let !ancestorHeight = maybe (genesisHeight v cid) (view blockHeight) commonAncestor
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
                    let forkStartHeight = maybe (genesisHeight v cid) (succ . view blockHeight) commonAncestor
                    in getBranchIncreasing bhdb parentHeaderOfHeaderToValidate (fromIntegral forkStartHeight) kont

        ((), results) <-
            withPactState $ \runPact ->
                withForkBlockStream $ \forkBlockHeaders -> do

                    -- given a header for a block in the fork, fetch its payload
                    -- and run its transactions, validating its hashes
                    let runForkBlockHeaders = Stream.map (\forkBh -> do
                            payload <- liftIO $ lookupPayloadWithHeight payloadDb (Just $ view blockHeight forkBh) (view blockPayloadHash forkBh) >>= \case
                                Nothing -> internalError
                                    $ "execValidateBlock: lookup of payload failed"
                                    <> ". BlockPayloadHash: " <> encodeToText (view blockPayloadHash forkBh)
                                    <> ". Block: " <> encodeToText (ObjectEncoded forkBh)
                                Just x -> return $ payloadWithOutputsToPayloadData x
                            void $ execBlock forkBh (CheckablePayload payload)
                            return ([], forkBh)
                            ) forkBlockHeaders

                    -- run the new block, the one we're validating, and
                    -- validate its hashes
                    let runThisBlock = Stream.yield $ do
                            !output <- execBlock headerToValidate payloadToValidate
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
            <$> lookupBlockHeader (view blockParent headerToValidate) "execValidateBlock"
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
    -> PactServiceM logger tbl (Historical (Maybe (P.TxLog P.RowData)))
execHistoricalLookup bh d k = pactLabel "execHistoricalLookup" $ do
  !cp <- view psCheckpointer
  liftIO $ _cpGetHistoricalLookup (_cpReadCp cp) bh d k

execPreInsertCheckReq
    :: (CanReadablePayloadCas tbl, Logger logger)
    => Vector ChainwebTransaction
    -> PactServiceM logger tbl (Vector (Either Mempool.InsertError ChainwebTransaction))
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
            pc <- view psParentHeader
            let
                parentTime = ParentCreationTime (view blockCreationTime $ _parentHeader pc)
                currHeight = succ $ view blockHeight $ _parentHeader pc
                v = _chainwebVersion pc
                cid = _chainId pc
            liftIO $ validateChainwebTxs logger v cid pdb parentTime currHeight txs
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
        -> Vector (Either InsertError ChainwebTransaction)
        -> PactBlockM logger tbl (Vector (Either InsertError ChainwebTransaction))
    attemptBuyGas miner txsOrErrs = localLabelBlock ("transaction", "attemptBuyGas") $ do
            mc <- getInitCache
            l <- view (psServiceEnv . psLogger)
            V.fromList . toList . sfst <$> V.foldM (buyGasFor l) (T2 mempty mc) txsOrErrs
      where
        buyGasFor :: logger
          -> T2 (DL.DList (Either InsertError ChainwebTransaction)) ModuleCache
          -> Either InsertError ChainwebTransaction
          -> PactBlockM logger tbl (T2 (DL.DList (Either InsertError ChainwebTransaction)) ModuleCache)
        buyGasFor _l (T2 dl mcache) err@Left {} = return (T2 (DL.snoc dl err) mcache)
        buyGasFor l (T2 dl mcache) (Right tx) = do
            T2 mcache' !res <- do
              let cmd = payloadObj <$> tx
                  gasPrice = view cmdGasPrice cmd
                  gasLimit = fromIntegral $ view cmdGasLimit cmd
                  txst = TransactionState
                      { _txCache = mcache
                      , _txLogs = mempty
                      , _txGasUsed = 0
                      , _txGasId = Nothing
                      , _txGasModel = P._geGasModel P.freeGasEnv
                      , _txWarnings = mempty
                      }
              let !nid = networkIdOf cmd
              let !rk = P.cmdToRequestKey cmd
              pd <- getTxContext (publicMetaOf cmd)
              bhdb <- view (psServiceEnv . psBlockHeaderDb)
              dbEnv <- view psBlockDbEnv
              spv <- pactSPV bhdb . _parentHeader <$> view psParentHeader
              let ec = P.mkExecutionConfig $
                    [ P.FlagDisableModuleInstall
                    , P.FlagDisableHistoryInTransactionalMode ] ++
                    disableReturnRTC (ctxVersion pd) (ctxChainId pd) (ctxCurrentBlockHeight pd)

              let buyGasEnv = TransactionEnv P.Transactional (_cpPactDbEnv dbEnv) l Nothing (ctxToPublicData pd) spv nid gasPrice rk gasLimit ec Nothing Nothing

              cr <- liftIO
                $! catchesPactError l CensorsUnexpectedError
                $! execTransactionM buyGasEnv txst
                $! buyGas pd cmd miner

              case cr of
                  Left err -> return (T2 mcache (Left (InsertErrorBuyGas (T.pack $ show err))))
                  Right t -> return (T2 (_txCache t) (Right tx))
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

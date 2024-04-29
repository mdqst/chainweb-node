{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

-- |
-- Chainweb.VerifierPlugin.Hyperlane.Message
-- Copyright: Copyright © 2024 Kadena LLC.
-- License: MIT
--
-- Verifier plugin for Hyperlane Message.
-- Verifies the message using the provided metadata.
--
module Chainweb.VerifierPlugin.Hyperlane.Message (plugin) where

import Control.Applicative
import Control.Error
import Control.Monad (unless, guard)
import Control.Monad.Except

import qualified Data.Text.Encoding as Text
import qualified Data.Vector as V
import qualified Data.Set as Set

import Ethereum.Misc hiding (Word256)

import Pact.Types.Runtime
import Pact.Types.PactValue
import Pact.Types.Capability

import Chainweb.Utils.Serialization (putRawByteString, runPutS, runGetS, putWord32be)

import Chainweb.Version.Guards
import Chainweb.VerifierPlugin
import Chainweb.VerifierPlugin.Hyperlane.Binary
import Chainweb.VerifierPlugin.Hyperlane.Utils
import Chainweb.Utils (encodeB64UrlNoPaddingText, decodeB64UrlNoPaddingText, sshow)

plugin :: VerifierPlugin
plugin = VerifierPlugin $ \(v, cid, bh) proof caps gasRef -> do
  -- extract capability values
  SigCapability{..} <- case Set.toList caps of
    [cap] -> return cap
    _ -> throwError $ VerifierError "Expected one capability."

  (capMessageBody, capRecipient, capSigners) <- case _scArgs of
      [mb, r, sigs] -> return (mb, r, sigs)
      _ -> throwError $ VerifierError $ "Incorrect number of capability arguments. Expected: messageBody, recipient, signers."

  -- extract proof object values
  (hyperlaneMessageBase64, metadataBase64) <- case proof of
    PList values
      | [PLiteral (LString msg), PLiteral (LString mtdt)] <- V.toList values ->
        pure (msg, mtdt)
    _ -> throwError $ VerifierError "Expected a proof data as a list"

  (HyperlaneMessage{..}, hyperlaneMessageBinary) <- do
    chargeGas gasRef 5
    msg <- decodeB64UrlNoPaddingText hyperlaneMessageBase64
    decoded <- runGetS getHyperlaneMessage msg
    return (decoded, msg)

  metadata <- do
    chargeGas gasRef 5
    metadataBytes <- decodeB64UrlNoPaddingText metadataBase64

    let
      getMerkleMetadata = guard (chainweb224Pact v cid bh) >> Right <$> getMerkleRootMultisigIsmMetadata
      getMessageIdMetadata = Left <$> getMessageIdMultisigIsmMetadata
    runGetS (getMerkleMetadata <|> getMessageIdMetadata) metadataBytes

  -- validate recipient
  let hmRecipientPactValue = PLiteral $ LString $ Text.decodeUtf8 hmRecipient
  unless (hmRecipientPactValue == capRecipient) $
    throwError $ VerifierError $
      "Recipients don't match. Expected: " <> sshow hmRecipientPactValue <> " but got " <> sshow capRecipient

  let
    hmMessageBodyPactValue = PLiteral $ LString $ encodeB64UrlNoPaddingText hmMessageBody

  unless (hmMessageBodyPactValue == capMessageBody) $
    throwError $ VerifierError $
      "Invalid TokenMessage. Expected: " <> sshow hmMessageBodyPactValue <> " but got " <> sshow capMessageBody

  -- validate signers
  let messageId = keccak256ByteString hyperlaneMessageBinary

  (originMerkleTreeAddress, root, checkpointIndex, messageId', signatures) <- case metadata of
    Right MerkleRootMultisigIsmMetadata{..} -> do
      chargeGas gasRef 18 -- gas cost of the `branchRoot`
      pure ( mrmimOriginMerkleTreeAddress
        , branchRoot messageId mrmimMerkleProof mrmimMessageIdIndex
        , mrmimSignedCheckpointIndex
        , mrmimSignedCheckpointMessageId
        , mrmimSignatures)
    Left MessageIdMultisigIsmMetadata{..} -> pure
      ( mmimOriginMerkleTreeAddress
      , mmimSignedCheckpointRoot
      , mmimSignedCheckpointIndex
      , messageId
      , mmimSignatures)

  let
    domainHash = keccak256ByteString $ runPutS $ do
      -- Corresponds to abi.encodePacked behaviour
      putWord32be hmOriginDomain
      putRawByteString originMerkleTreeAddress
      putRawByteString "HYPERLANE"

  let
    digest = keccak256 $ runPutS $ do
      -- Corresponds to abi.encodePacked behaviour
      putRawByteString ethereumHeader
      putRawByteString $
        keccak256ByteString $ runPutS $ do
          putRawByteString domainHash
          putRawByteString root
          putWord32be checkpointIndex
          putRawByteString messageId'

  addresses <- catMaybes <$> mapM (\sig -> chargeGas gasRef 16250 >> recoverAddress digest sig) signatures
  let addressesVals = PList $ V.fromList $ map (PLiteral . LString . encodeHex) addresses

  -- Note, that we check the signers for the full equality including their order and amount.
  -- Hyperlane's ISM uses a threshold and inclusion check.
  unless (addressesVals == capSigners) $
    throwError $ VerifierError $
      "Signers don't match. Expected: " <> sshow addressesVals <> " but got " <> sshow capSigners

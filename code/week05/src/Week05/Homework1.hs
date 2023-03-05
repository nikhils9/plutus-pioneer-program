{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module Week05.Homework1 where

import           Control.Monad              hiding (fmap)
import           Control.Monad.Freer.Extras as Extras
import           Data.Aeson                 (ToJSON, FromJSON)
import           Data.Default               (Default (..))
import           Data.Text                  (Text)
import           Data.Void                  (Void)
import           GHC.Generics               (Generic)
import           Plutus.Contract            as Contract
import           Plutus.Trace.Emulator      as Emulator
import qualified PlutusTx
import           PlutusTx.Prelude           hiding (Semigroup(..), unless)
import           Ledger                     hiding (mint, singleton)
import           Ledger.Constraints         as Constraints
import           Ledger.TimeSlot
import qualified Ledger.Typed.Scripts       as Scripts
import           Ledger.Value               as Value
import           Playground.Contract        (printJson, printSchemas, ensureKnownCurrencies, stage, ToSchema)
import           Playground.TH              (mkKnownCurrencies, mkSchemaDefinitions)
import           Playground.Types           (KnownCurrency (..))
import           Prelude                    (IO, Semigroup (..), Show (..), String, undefined)
import           Text.Printf                (printf)
import           Wallet.Emulator.Wallet

{-# INLINABLE mkPolicy #-}
-- This policy should only allow minting (or burning) of tokens if the owner of the specified PaymentPubKeyHash
-- has signed the transaction and if the specified deadline has not passed.
mkPolicy :: PaymentPubKeyHash -> POSIXTime -> () -> ScriptContext -> Bool
mkPolicy pkh deadline () ctx = 
    traceIfFalse "You are not the owner of this token" isOwner &&
    traceIfFalse "The deadline has passed" withinDeadline
    where
        info = scriptContextTxInfo ctx

        withinDeadline = contains (to deadline) $ txInfoValidRange info

        isOwner = txSignedBy info $ unPaymentPubKeyHash pkh


policy :: PaymentPubKeyHash -> POSIXTime -> Scripts.MintingPolicy
policy pkh deadline = 
    mkMintingPolicyScript $
    $$(PlutusTx.compile [|| \p' d' -> Scripts.wrapMintingPolicy $ mkPolicy p' d' ||])
    `PlutusTx.applyCode`
    PlutusTx.liftCode pkh
    `PlutusTx.applyCode`
    PlutusTx.liftCode deadline

curSymbol :: PaymentPubKeyHash -> POSIXTime -> CurrencySymbol
curSymbol pkh deadline = scriptCurrencySymbol $ policy pkh deadline

data MintParams = MintParams
    { mpTokenName :: !TokenName
    , mpDeadline  :: !POSIXTime
    , mpAmount    :: !Integer
    , mpPaymentPubKeyHash :: !PaymentPubKeyHash
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

type SignedSchema = Endpoint "mint" MintParams

mint :: MintParams -> Contract w SignedSchema Text ()
mint mp = do
    now <- Contract.currentTime
    let 
        deadline = mpDeadline mp
        pkh = mpPaymentPubKeyHash mp
    if now > deadline
        then Contract.logError @String "deadline passed"
        else do
            let val     = Value.singleton (curSymbol pkh deadline) (mpTokenName mp) (mpAmount mp)
                lookups = Constraints.mintingPolicy $ policy pkh deadline
                tx      = Constraints.mustMintValue val <> Constraints.mustValidateIn (to $ now + 60000)
            ledgerTx <- submitTxConstraintsWith @Void lookups tx
            void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
            Contract.logInfo @String $ printf "forged %s" (show val)

endpoints :: Contract () SignedSchema Text ()
endpoints = mint' >> endpoints
  where
    mint' = awaitPromise $ endpoint @"mint" mint

mkSchemaDefinitions ''SignedSchema

mkKnownCurrencies []

test :: IO ()
test = runEmulatorTraceIO $ do
    let tn       = "ABC"
        deadline = slotToBeginPOSIXTime def 100
        pkh = mockWalletPaymentPubKeyHash (knownWallet 1)
    h <- activateContractWallet (knownWallet 1) endpoints
    callEndpoint @"mint" h $ MintParams
        { mpTokenName = tn
        , mpDeadline  = deadline
        , mpAmount    = 555
        , mpPaymentPubKeyHash = pkh
        }
    void $ Emulator.waitNSlots 110
    callEndpoint @"mint" h $ MintParams
        { mpTokenName = tn
        , mpDeadline  = deadline
        , mpAmount    = 555
        , mpPaymentPubKeyHash = pkh
        }
    void $ Emulator.waitNSlots 1

test1 :: IO ()
test1 = runEmulatorTraceIO $ do
    let 
        tn = "NFT"
        deadline = slotToBeginPOSIXTime def 100
        pkh = mockWalletPaymentPubKeyHash (knownWallet 1)

    h1 <- activateContractWallet (knownWallet 1) endpoints
    callEndpoint @"mint" h1 $ MintParams {
        mpTokenName = tn,
        mpDeadline = deadline,
        mpAmount = 500,
        mpPaymentPubKeyHash = pkh
    }
    void $ Emulator.waitNSlots 1

    h2 <- activateContractWallet (knownWallet 2) endpoints
    callEndpoint @"mint" h2 $ MintParams {
        mpTokenName = tn,
        mpDeadline = deadline,
        mpAmount = 500,
        mpPaymentPubKeyHash = pkh
    }
    void $ Emulator.waitNSlots 1

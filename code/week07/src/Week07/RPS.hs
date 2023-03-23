{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Week07.RPS
    ( Game (..)
    , GameChoice (..)
    , FirstParams (..)
    , SecondParams (..)
    , GameSchema
    , Last (..)
    , ThreadToken
    , Text
    , endpoints
    ) where

import           Control.Monad                hiding (fmap)
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.Monoid                  (Last (..))
import           Data.Text                    (Text, pack)
import           GHC.Generics                 (Generic)
import           Ledger                       hiding (singleton)
import           Ledger.Ada                   as Ada
import           Ledger.Constraints           as Constraints
import           Ledger.Typed.Tx
import qualified Ledger.Typed.Scripts         as Scripts
import           Plutus.Contract              as Contract
import           Plutus.Contract.StateMachine
import qualified PlutusTx
import           PlutusTx.Prelude             hiding (Semigroup(..), check, unless)
import           Playground.Contract          (ToSchema)
import           Prelude                      (Semigroup (..), Show (..), String)
import qualified Prelude

data Game = Game
    { gFirst          :: !PaymentPubKeyHash
    , gSecond         :: !PaymentPubKeyHash
    , gStake          :: !Integer
    , gPlayDeadline   :: !POSIXTime
    , gRevealDeadline :: !POSIXTime
    , gToken          :: !ThreadToken
    } deriving (Show, Generic, FromJSON, ToJSON, Prelude.Eq)

PlutusTx.makeLift ''Game

data GameChoice = Rock | Paper | Scissors
    deriving (Show, Generic, FromJSON, ToJSON, ToSchema, Prelude.Eq, Prelude.Ord)

instance Eq GameChoice where
    {-# INLINABLE (==) #-}
    Rock == Rock = True
    Paper  == Paper  = True
    Scissors == Scissors = True
    _ == _    = False

PlutusTx.unstableMakeIsData ''GameChoice

data GameDatum = GameDatum BuiltinByteString (Maybe GameChoice) | Finished
    deriving Show

instance Eq GameDatum where
    {-# INLINABLE (==) #-}
    GameDatum bs mc == GameDatum bs' mc' = (bs == bs') && (mc == mc')
    Finished        == Finished          = True
    _               == _                 = False

PlutusTx.unstableMakeIsData ''GameDatum

data GameRedeemer = Play GameChoice | RevealVictory BuiltinByteString | RevealDraw BuiltinByteString 
                    | ClaimFirst | ClaimSecond
    deriving Show

PlutusTx.unstableMakeIsData ''GameRedeemer

{-# INLINABLE lovelaces #-}
lovelaces :: Value -> Integer
lovelaces = Ada.getLovelace . Ada.fromValue

{-# INLINABLE gameDatum #-}
gameDatum :: TxOut -> (DatumHash -> Maybe Datum) -> Maybe GameDatum
gameDatum o f = do
    dh      <- txOutDatum o
    Datum d <- f dh
    PlutusTx.fromBuiltinData d

{-# INLINABLE transition #-}
transition :: Game -> State GameDatum -> GameRedeemer -> Maybe (TxConstraints Void Void, State GameDatum)
transition game s r = case (stateValue s, stateData s, r) of
    (v, GameDatum bs Nothing, Play c)
        | lovelaces v == gStake game         -> Just ( Constraints.mustBeSignedBy (gSecond game)                    <>
                                                       Constraints.mustValidateIn (to $ gPlayDeadline game)
                                                     , State (GameDatum bs $ Just c) (lovelaceValueOf $ 2 * gStake game)
                                                     )
    (v, GameDatum _ (Just _), RevealVictory _)
        | lovelaces v == (2 * gStake game)   -> Just ( Constraints.mustBeSignedBy (gFirst game)                     <>
                                                       Constraints.mustValidateIn (to $ gRevealDeadline game)
                                                     , State Finished mempty
                                                     )
    (v, GameDatum _ (Just _), RevealDraw _)
        | lovelaces v == (2 * gStake game)  ->  Just ( Constraints.mustBeSignedBy (gFirst game) <>
                                                       Constraints.mustValidateIn (to $ gRevealDeadline game) <>
                                                       Constraints.mustPayToPubKey (gSecond game) (Ada.lovelaceValueOf $ gStake game)
                                                     , State Finished mempty 
                                                     )
    (v, GameDatum _ Nothing, ClaimFirst)
        | lovelaces v == gStake game         -> Just ( Constraints.mustBeSignedBy (gFirst game)                     <>
                                                       Constraints.mustValidateIn (from $ 1 + gPlayDeadline game)
                                                     , State Finished mempty
                                                     )
    (v, GameDatum _ (Just _), ClaimSecond)
        | lovelaces v == (2 * gStake game)   -> Just ( Constraints.mustBeSignedBy (gSecond game)                    <>
                                                       Constraints.mustValidateIn (from $ 1 + gRevealDeadline game)
                                                     , State Finished mempty
                                                     )
    _                                        -> Nothing

{-# INLINABLE final #-}
final :: GameDatum -> Bool
final Finished = True
final _        = False

{-# INLINABLE gameOrder #-}
gameOrder :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString -> GameChoice -> BuiltinByteString
gameOrder _ bsPaper' _ Rock = bsPaper'
gameOrder _ _ bsScissors' Paper = bsScissors'
gameOrder bsRock' _ _ Scissors = bsRock'

{-# INLINABLE gameChoiceBS #-}
gameChoiceBS :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString -> GameChoice -> BuiltinByteString
gameChoiceBS bsRock' _ _ Rock = bsRock'
gameChoiceBS _ bsPaper' _ Paper = bsPaper'
gameChoiceBS _ _ bsScissors' Scissors = bsScissors'

gameWon :: GameChoice -> GameChoice -> Bool
gameWon Rock Scissors = True
gameWon Scissors Paper = True
gameWon Paper Rock = True
gameWon _ _ = False

{-# INLINABLE check #-}
check :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString -> GameDatum -> GameRedeemer -> ScriptContext -> Bool
check bsRock' bsPaper' bsScissors' (GameDatum bs (Just c)) (RevealVictory nonce) _ =
    sha2_256 (nonce `appendByteString` (gameOrder bsRock' bsPaper' bsScissors' c))    == bs
check bsRock' bsPaper' bsScissors' (GameDatum bs (Just c)) (RevealDraw nonce) _ =
    sha2_256 (nonce `appendByteString` (gameChoiceBS bsRock' bsPaper' bsScissors' c)) == bs
check _       _      _                       _                     _             _ = True

{-# INLINABLE gameStateMachine #-}
gameStateMachine :: Game -> BuiltinByteString -> BuiltinByteString -> BuiltinByteString -> StateMachine GameDatum GameRedeemer
gameStateMachine game bsRock' bsPaper' bsScissors' = StateMachine
    { smTransition  = transition game
    , smFinal       = final
    , smCheck       = check bsRock' bsPaper' bsScissors'
    , smThreadToken = Just $ gToken game
    }

{-# INLINABLE mkGameValidator #-}
mkGameValidator :: Game -> BuiltinByteString -> BuiltinByteString -> BuiltinByteString -> GameDatum -> GameRedeemer -> ScriptContext -> Bool
mkGameValidator game bsRock' bsPaper' bsScissors' = mkValidator $ gameStateMachine game bsRock' bsPaper' bsScissors'

type Gaming = StateMachine GameDatum GameRedeemer

bsRock, bsPaper, bsScissors :: BuiltinByteString
bsRock = "R"
bsPaper  = "P"
bsScissors = "S"

gameStateMachine' :: Game -> StateMachine GameDatum GameRedeemer
gameStateMachine' game = gameStateMachine game bsRock bsPaper bsScissors

typedGameValidator :: Game -> Scripts.TypedValidator Gaming
typedGameValidator game = Scripts.mkTypedValidator @Gaming
    ($$(PlutusTx.compile [|| mkGameValidator ||])
        `PlutusTx.applyCode` PlutusTx.liftCode game
        `PlutusTx.applyCode` PlutusTx.liftCode bsRock
        `PlutusTx.applyCode` PlutusTx.liftCode bsPaper
        `PlutusTx.applyCode` PlutusTx.liftCode bsScissors)
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @GameDatum @GameRedeemer

gameValidator :: Game -> Validator
gameValidator = Scripts.validatorScript . typedGameValidator

gameAddress :: Game -> Ledger.Address
gameAddress = scriptAddress . gameValidator

gameClient :: Game -> StateMachineClient GameDatum GameRedeemer
gameClient game = mkStateMachineClient $ StateMachineInstance (gameStateMachine' game) (typedGameValidator game)

data FirstParams = FirstParams
    { fpSecond         :: !PaymentPubKeyHash
    , fpStake          :: !Integer
    , fpPlayDeadline   :: !POSIXTime
    , fpRevealDeadline :: !POSIXTime
    , fpNonce          :: !BuiltinByteString
    , fpChoice         :: !GameChoice
    } deriving (Show, Generic, FromJSON, ToJSON, ToSchema)

mapError' :: Contract w s SMContractError a -> Contract w s Text a
mapError' = mapError $ pack . show

waitUntilTimeHasPassed :: AsContractError e => POSIXTime -> Contract w s e ()
waitUntilTimeHasPassed t = void $ awaitTime t >> waitNSlots 1

firstGame :: forall s. FirstParams -> Contract (Last ThreadToken) s Text ()
firstGame fp = do
    pkh <- Contract.ownPaymentPubKeyHash
    tt  <- mapError' getThreadToken
    let game   = Game
            { gFirst          = pkh
            , gSecond         = fpSecond fp
            , gStake          = fpStake fp
            , gPlayDeadline   = fpPlayDeadline fp
            , gRevealDeadline = fpRevealDeadline fp
            , gToken          = tt
            }
        client = gameClient game
        v      = lovelaceValueOf (fpStake fp)
        c      = fpChoice fp
        bs     = sha2_256 $ fpNonce fp `appendByteString` (gameChoiceBS bsRock bsPaper bsScissors c)
    void $ mapError' $ runInitialise client (GameDatum bs Nothing) v
    logInfo @String $ "made first move: " ++ show (fpChoice fp)
    tell $ Last $ Just tt

    waitUntilTimeHasPassed $ fpPlayDeadline fp

    m <- mapError' $ getOnChainState client
    case m of
        Nothing     -> throwError "game output not found"
        Just (o, _) -> case tyTxOutData $ ocsTxOut o of

            GameDatum _ Nothing -> do
                logInfo @String "second player did not play"
                void $ mapError' $ runStep client ClaimFirst
                logInfo @String "first player reclaimed stake"

            GameDatum _ (Just c') | c' == c -> do
                logInfo @String "second player played and both drawed"
                void $ mapError' $ runStep client $ RevealDraw $ fpNonce fp
                logInfo @String "first player revealed and both drawed"

            GameDatum _ (Just c') | gameWon c c' -> do
                logInfo @String "second player played and lost"
                void $ mapError' $ runStep client $ RevealVictory $ fpNonce fp
                logInfo @String "first player revealed and won"

            _ -> logInfo @String "second player played and won"

data SecondParams = SecondParams
    { spFirst          :: !PaymentPubKeyHash
    , spStake          :: !Integer
    , spPlayDeadline   :: !POSIXTime
    , spRevealDeadline :: !POSIXTime
    , spChoice         :: !GameChoice
    , spToken          :: !ThreadToken
    } deriving (Show, Generic, FromJSON, ToJSON)

secondGame :: forall w s. SecondParams -> Contract w s Text ()
secondGame sp = do
    pkh <- Contract.ownPaymentPubKeyHash
    let game   = Game
            { gFirst          = spFirst sp
            , gSecond         = pkh
            , gStake          = spStake sp
            , gPlayDeadline   = spPlayDeadline sp
            , gRevealDeadline = spRevealDeadline sp
            , gToken          = spToken sp
            }
        client = gameClient game
    m <- mapError' $ getOnChainState client
    case m of
        Nothing          -> logInfo @String "no running game found"
        Just (o, _) -> case tyTxOutData $ ocsTxOut o of
            GameDatum _ Nothing -> do
                logInfo @String "running game found"
                void $ mapError' $ runStep client $ Play $ spChoice sp
                logInfo @String $ "made second move: " ++ show (spChoice sp)

                waitUntilTimeHasPassed $ spRevealDeadline sp

                m' <- mapError' $ getOnChainState client
                case m' of
                    Nothing -> logInfo @String "first player won"
                    Just _  -> do
                        logInfo @String "first player didn't reveal"
                        void $ mapError' $ runStep client ClaimSecond
                        logInfo @String "second player won"

            _ -> throwError "unexpected datum"

type GameSchema = Endpoint "first" FirstParams .\/ Endpoint "second" SecondParams

endpoints :: Contract (Last ThreadToken) GameSchema Text ()
endpoints = awaitPromise (first `select` second) >> endpoints
  where
    first  = endpoint @"first"  firstGame
    second = endpoint @"second" secondGame

{-# LANGUAGE OverloadedStrings #-}
import Language.Marlowe.Extended

main :: IO ()
main = print . pretty $ contract' "Alice" "Bob" "Charlie" $ Constant 100

choiceId :: Party -> ChoiceId
choiceId p = ChoiceId "Winner" p

{- When the Mediator (charlie) has to deposit in the beginning to start the game 
so that if he does not choose, each player gets half of his deposit -}
contract' :: Party -> Party -> Party -> Value -> Contract
contract' alice bob charlie deposit@(Constant x) =
    When [
        Case 
            (Deposit charlie charlie ada (Constant $ 2 * x))
            (contract alice bob charlie deposit)
    ]
    100 Close

contract :: Party -> Party -> Party -> Value -> Contract
contract alice bob charlie deposit =
    When
        [ f alice bob
        , f bob alice
        ]
        10 Close
  where
    f :: Party -> Party -> Case
    f x y =
        Case
            (Deposit
                x
                x
                ada
                deposit
            )
            (When
                [Case
                    (Deposit
                        y
                        y
                        ada
                        deposit
                    )
                    (When
                        [Case
                            (Choice
                                (choiceId charlie)
                                [Bound 1 2]
                            )
                            (If
                                (ValueEQ
                                    (ChoiceValue $ choiceId charlie)
                                    (Constant 1)
                                )
                                (Pay
                                    bob
                                    (Account alice)
                                    ada
                                    deposit
                                    Close
                                )
                                (Pay
                                    alice
                                    (Account bob)
                                    ada
                                    deposit
                                    Close
                                )
                            )]
                        30 (
                            Pay charlie (Account alice) ada deposit (Pay charlie (Account bob) ada deposit Close)
                        )
                    )]
                20 Close
            )


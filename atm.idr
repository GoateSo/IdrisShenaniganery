-- chapter 14.2 ATM state machine
import Data.Vect

Pin : Type
Pin =  Vect 4 Char

data ATMState =  Ready | CardInserted | Session
data PinCheck = Correct | Incorrect

||| predicate for all states in which EjectCard is possible
data HasCard : ATMState -> Type where
    HasCard_Inserted : HasCard CardInserted
    HasCard_Session : HasCard Session

data ATMCmd : (ty : Type) -> ATMState -> (handler : (ty -> ATMState)) -> Type where
    InsertCard : ATMCmd () Ready (const CardInserted)
    EjectCard :  {auto prf : HasCard st} -> ATMCmd () st (const Ready)
    GetPin :     ATMCmd Pin CardInserted (const CardInserted)
    CheckPin :   Pin -> ATMCmd PinCheck CardInserted
                    (\check => case check of
                        Correct => Session
                        Incorrect => CardInserted)
    GetAmount :  ATMCmd Nat st (const st)
    Dispense : Nat -> ATMCmd () Session (const Session)
    Message : String -> ATMCmd () st (const st)
    Pure : (res : ty) -> ATMCmd ty (stHandler res) stHandler
    (>>=) : ATMCmd a st1 st_fn2
        -> ((res : a) -> ATMCmd b (st_fn2 res) st_fn3)
        -> ATMCmd b st1 st_fn3


atmcmd : ATMCmd () Ready (const Ready)
atmcmd = do
    InsertCard
    x <- CheckPin !GetPin
    case x of
        Correct => do
            Dispense !GetAmount
            EjectCard
        Incorrect => do
            Message "incorrect pin given"
            EjectCard

atmCmd2 : ATMCmd () Ready (const Ready)
atmCmd2 = do
    EjectCard

testPin : Pin
testPin = ['1','2','3','4']

readVect : (n : Nat) -> IO (Vect n Char)
readVect Z = do
    discard <- getLine
    pure []
readVect (S k) = do
    c <- getChar
    chs <- readVect k
    pure (c :: chs)

runATM : ATMCmd res iState handler -> IO res
runATM InsertCard = do
    putStrLn "insert card (press enter)"
    _ <- getLine
    pure ()
runATM EjectCard = putStrLn "ejected card"
runATM GetPin = do
    putStrLn "insert pin"
    readVect 4
runATM (CheckPin pin) =
    if pin == testPin
        then pure Correct
        else pure Incorrect
runATM GetAmount = do
    putStrLn "how much?"
    x <- getLine
    pure $ cast x
runATM (Dispense amt) = do
    putStrLn ("dispensing... " ++ (show amt) ++ " dollars")
    pure ()
runATM (Message x) = putStrLn x
runATM (Pure res) = pure res
runATM (x >>= f) = do
    x' <- runATM x
    runATM (f x')

main : IO ()
main = runATM atmcmd

--from Chapter 9 of Type Driven Programming with Idris
import Data.Vect

data WordState : (remainingGuess : Nat) -> (letters : Nat) -> Type where
    MkWordState : (word : String) ->
                  (missing : Vect letters Char) ->
                  WordState remainingGuess letters

data Finished : Type where
    Lost  : (game : WordState 0 (S letters)) -> Finished
    Won   : (game : WordState (S guesses) 0) -> Finished


data ValidInput : List Char -> Type where
    Letter : (c : Char) -> ValidInput [c]


removeElem' : (val : a) -> (xs : Vect (S n) a) -> (prf : Elem val xs) -> Vect n a
removeElem' val (val :: ys) Here = ys
removeElem' {n = Z} val (y :: []) (There later) = absurd later
removeElem' {n = (S k)} val (y :: ys) (There later) = y :: removeElem' val ys later

removeElem : (val : a) -> (xs : Vect (S n) a) -> {auto prf : Elem val xs} -> Vect n a
removeElem val xs {prf} = removeElem' val xs prf


emptyInvalid : ValidInput [] -> Void
emptyInvalid (Letter _) impossible

consInvalid : ValidInput (x :: y :: xs) -> Void
consInvalid (Letter _) impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No emptyInvalid
isValidInput (x :: []) = Yes (Letter x)
isValidInput (x :: y :: xs) = No consInvalid

isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput (unpack s)

|||get letter from input and check validity
readGuess : IO (x ** ValidInput x)
readGuess = do putStr "Guess:"
               x <- getLine
               case isValidString(toUpper x) of
                   (Yes prf) => pure (_ ** prf)
                   (No contra) => do putStrLn "Invalid guess"
                                     readGuess

processGuess : (letter : Char) ->
                WordState (S guesses) (S letters) ->
                Either (WordState guesses (S letters))
                        (WordState (S guesses) letters)
processGuess letter (MkWordState word missing)
            = case isElem letter missing of
                  (Yes prf) => Right (MkWordState word (removeElem letter missing))
                  (No contra) => Left (MkWordState word missing)

game : WordState (S guesses) (S letters) -> IO Finished
game {guesses} {letters} st
    = do
        (_ ** Letter letter) <- readGuess
        case processGuess letter st of
            (Left l) => do
                          putStrLn "Wrong"
                          case guesses of
                             Z => pure (Lost l)
                             (S k) => game l
            (Right r) => do
                          putStrLn "Right"
                          case letters of
                             Z => pure (Won r)
                             (S k) => game r


main : IO ()
main = do result <- game {guesses = 2} (MkWordState "Ligma" ['L', 'I'])
          case result of
              (Lost game) => putStrLn "you lost"
              (Won game) => putStrLn "you won"

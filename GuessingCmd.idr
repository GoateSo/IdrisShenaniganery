--chapter 13.1
--exercise 2
-- data GuessCmd : Type -> Nat -> Nat -> Type where
--     Try : Integer -> GuessCmd Ordering (S k) (k)
--
--     Pure : ty -> GuessCmd ty state state
--
--     (>>=) : GuessCmd a state1 state2 ->
--             (a -> GuessCmd b state2 state3) ->
--             GuessCmd b state1 state3
-- changed in chapter 14.3

import Data.Vect

data Result = Right | Wrong

data GameState : Type where
    NotRunning : GameState
    Running : (guesses : Nat) -> (letters : Nat) -> GameState

data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
    -- core functionality
    NewGame : (word : String)
    -> GameCmd () NotRunning (const (Running 6 (length $ nub $ unpack word)))
    Won : GameCmd () (Running (S k) Z) (const NotRunning)
    Lost : GameCmd () (Running Z (S k)) (const NotRunning)
    Guess : (guess : Char) -> GameCmd Result (Running (S k) (S n))
        (\res =>
            case res of
                Wrong => Running k (S n)
                Right => Running (S k) n
        )

    --combinators
    Pure : (res : ty) -> GameCmd ty (fn res) fn
    (>>=) : GameCmd a state1 handler1
    -> ((res : a) -> GameCmd b (handler1 res) handler2)
    -> GameCmd b state1 handler2

    -- user interactions
    ShowState : GameCmd () state (const state)
    Message   : String -> GameCmd () state (const state)
    ReadGuess : GameCmd Char state (const state)

namespace Loop
    data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
        (>>=) : GameCmd a st1 stfn
            -> ((res : a) -> Inf (GameLoop b (stfn res) stfn2))
            -> GameLoop b st1 stfn2
        Exit : GameLoop () NotRunning (const NotRunning)

gameLoop : GameLoop () (Running (S guesses) (S chars)) (const NotRunning)
gameLoop {guesses} {chars} = do
    ShowState
    ok <- Guess !ReadGuess
    case ok of
        Wrong => case guesses of
            Z => do
                Lost
                Message "u lost lol"
                Exit
            S k => do
                Message "try again"
                gameLoop
        Right => case chars of
            Z => do -- no characters remaining
                Won
                ShowState
                Exit
            S k => do
                Message "correct! go again"
                ShowState
                gameLoop
                -- ?rh3s

data Game : GameState -> Type where
    GameStart : Game NotRunning
    GameWon : (word : String) -> Game NotRunning
    GameLost : (word : String) -> Game NotRunning
    InProgress : (word : String) -> (guesses : Nat)
                -> (missing : Vect letters Char)
                -> Game (Running guesses letters)


-- a : GuessCmd () 3 0
-- a = do Try 20
--        Try 15
--        Try 10
--        Pure ()

-- --should error
-- b : GuessCmd () 0 0
-- b = do Try 1
--        Pure ()


--exercise 3
-- data Matter = Solid | Liquid | Gas
--
-- data MatterCmd : Type -> Matter -> Matter -> Type where
--     Melt : MatterCmd () Solid Liquid
--     Condense : MatterCmd () Gas Liquid
--     Freeze : MatterCmd () Liquid Solid
--     Boil : MatterCmd () Liquid Gas
--
--     Bind : MatterCmd a s1 s2 -> (a -> MatterCmd b s2 s3) -> MatterCmd b s1 s
--
-- namespace MatterBind
--     (>>=) : MatterCmd a s1 s2 -> (a -> MatterCmd b s2 s3) -> MatterCmd b s1 s
--     (>>=) = Bind
--
-- iceSteam : MatterCmd () Solid Gas
-- iceSteam = do Melt
--               Boil
--
-- steamIce : MatterCmd () Gas Solid
-- steamIce = do Condense
--               Freeze

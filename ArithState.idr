--chapter 12.3
--redesign of earlier arithmetic stream game with state Monad

import System
import MyState
import Data.Primitives.Views

%default total

|||contains information about the amount of questions answered right vs total
record Score where
    constructor MkScore
    correct : Nat
    attempted : Nat

|||holds relevant state for game
record GameState where
    constructor MkGameState
    score : Score
    difficulty : Int

Show Score where
  show s = (show $ correct $ s) ++ "/" ++ (show $ attempted $ s)

Show GameState where
  show s = (show $ score s) ++ "\n" ++
           "Difficulty: " ++ (show $ difficulty s)

||| default game state
initState : GameState
initState = MkGameState (MkScore 0 0) 12

|||limited list of relevant game Command
data Command : Type -> Type where
    PutStr : String -> Command ()
    GetLine : Command String

    GetRandom : Command Int
    GetGameState : Command GameState
    PutGameState : GameState -> Command ()

    Pure : ty -> Command ty
    Bind : Command a -> (a -> Command b) -> Command b

--exercise 2
--non mutual definition
-- Functor Command where
--     map f fa = Bind fa (\x => Pure (f x))
--
-- Applicative Command where
--     pure = Pure
--     f <*> fa = do func <- f
--                   x <- fa
--                   Pure (func x)
--
-- Monad Command where
--     (>>=) = Bind

--mutual definition
mutual
    Functor Command where
        map f fa = pure (f !fa)

    Applicative Command where
        pure = Pure
        f <*> fa = pure (!f !fa)

    Monad Command where
        (>>=) = Bind


data ConsoleIO : Type -> Type where
    Quit : a -> ConsoleIO a
    Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

data Input = Answer Int
           | QuitCmd


namespace ConsoleBind
    (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
    (>>=) = Do

-- --multiple impls of record mutation
-- namespace naive
--     --very boilerplate heavy
--     setDifficulty : Nat -> GameState -> GameState
--     setDifficulty newDiff (MkGameState score _) = MkGameState score newDiff
--
--     --alright, but still cumbersome to map operations
--     addWrong : GameState -> GameState
--     addWrong state = record { score->attempted = attempted (score state) + 1 } state
--
--     --see above
--     addCorrect : GameState -> GameState
--     addCorrect state = record { score->correct = correct (score state) + 1,
--                                 score->attempted = attempted (score state) + 1 } state

namespace idiomatic
    --takes advantage of record updates being first class
    --record { difficulty = newDiff } state
    --             1          2         3
    -- 1 = field to update
    -- 2 = new value
    -- 3 = record to update
    setDifficulty : Int -> GameState -> GameState
    setDifficulty newDiff = record { difficulty = newDiff }

    addWrong : GameState -> GameState
    addWrong = record {score -> attempted $= (+1)}

    addCorrect : GameState -> GameState
    addCorrect = record {score -> correct $= (+1),
                         score -> attempted $= (+1)}

-- runCommand : Command a -> IO a
-- runCommand (PutStr x) = putStr x
-- runCommand GetLine = getLine
-- runCommand (Pure val) = pure val
-- runCommand (Bind c f) = do res <- runCommand c
--                            runCommand (f res)
-- runCommand (PutGameState x) = ?runCommand_rhs_1
-- runCommand GetGameState = ?runCommand_rhs_2
-- runCommand GetRandom = ?runCommand_rhs_3

runCommand : Stream Int ->
             GameState ->
             Command a ->
             IO (a, Stream Int, GameState)
runCommand rnds state (PutStr x) = do putStr x
                                      pure ((), rnds, state)
runCommand rnds state GetLine = pure (!getLine, rnds, state)

runCommand (v::rest) state GetRandom
    = pure (getRandom v (difficulty state), rest, state) where
        getRandom : Int -> Int -> Int
        getRandom val max with (divides val max)
            getRandom val 0 | DivByZero = 1
            getRandom ((max * div) + rem) max | (DivBy prf) = abs rem + 1

runCommand rnds state GetGameState = pure (state, rnds, state)
runCommand rnds state (PutGameState x) = pure ((), rnds, x)
runCommand rnds state (Pure x) = pure (x, rnds, state)
runCommand rnds state (Bind x f) = do (res, newrnds, newst) <- runCommand rnds state x
                                      runCommand newrnds newst (f res)



readInput : (prompt : String) -> Command Input
readInput prompt = do PutStr prompt
                      answer <- GetLine
                      if toLower answer == "quit"
                          then Pure QuitCmd
                          else Pure (Answer (cast answer))

--exercise 1
updateGameState : (GameState -> GameState) -> Command()
updateGameState f = PutGameState (f !GetGameState)


mutual
    correct : ConsoleIO GameState
    correct = do PutStr "Correct!\n"
                 --PutGameState $ addCorrect !GetGameState
                 updateGameState addCorrect
                 quiz

    wrong  : Int -> ConsoleIO GameState
    wrong ans = do PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
                   --PutGameState $ addWrong !GetGameState
                   updateGameState addWrong
                   quiz

    quiz : ConsoleIO GameState
    quiz = do n1 <- GetRandom
              n2 <- GetRandom
              st <- GetGameState
              PutStr (show st ++ "\n")
              case !(readInput (show n1 ++ " * " ++ show n2 ++ " = " )) of
                  (Answer x) => if x == n1 * n2
                                    then correct
                                    else wrong (n1 * n2)
                  QuitCmd => Quit st

data Count = None | More (Lazy Count)

partial
forever : Count
forever = More forever

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   (seed' `shiftR` 2) :: randoms seed'


run : Count -> Stream Int -> GameState -> ConsoleIO a -> IO (Maybe a, Stream Int, GameState)
run x xs st (Quit val) = pure (Just val, xs, st)
run (More fuel) xs st (Do c f)
    = do (res, newRnds, newState) <- runCommand xs st c
         run fuel newRnds newState (f res)
run None xs st p = pure (Nothing, xs, st)

partial
main : IO ()
main = do seed <- time
          (Just score, _, state) <-
              run forever (randoms $ fromInteger seed) initState quiz
                  | _ => putStrLn  "Ran Out of Fuel" --see listing 5.6 in book for what this is
          putStrLn ("Final Score: " ++ show state)



record Votes where
    constructor MkVotes
    upvotes : Integer
    downvotes : Integer

record Article where
    constructor MkArticle
    title : String
    url : String
    score : Votes

initPage : (title : String) -> (url : String) -> Article
initPage title url = MkArticle title url (MkVotes 0 0)

badSite : Article
badSite = MkArticle "Bad Page" "http://example.com/bad" (MkVotes 5 47)

goodSite : Article
goodSite = MkArticle "Good Page" "http://example.com/good" (MkVotes 101 7)

--exercise 3
getScore : Article -> Integer
getScore x = let v = score x in
             upvotes v - downvotes v

--exercise 4
addUpvote : Article -> Article
addUpvote = record {score -> upvotes $= (+1)}

addDownvote : Article -> Article
addDownvote = record {score -> downvotes $= (+1)}

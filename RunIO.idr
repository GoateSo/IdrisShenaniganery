-- for chapter 11.3 of Type Driven Development with Idris
%default total

data Count = None | More (Lazy Count)

partial
forever : Count
forever = More forever

namespace RunIO
    data RunIO : Type -> Type where
        Quit : a -> RunIO a
        Do : IO a -> (a -> Inf (RunIO b)) -> RunIO b

    run : Count -> RunIO a -> IO (Maybe a)
    run _ (Quit val) = pure $ Just val
    run None (Do z f) = pure Nothing
    run (More x) (Do z f) = do res <- z
                               run x (f res)

namespace ConsoleIO
    data Command : Type -> Type where
        PutStr : String -> Command ()
        GetLine : Command String
        --expand featureset (11.3.3)
        Pure : a -> Command a
        Bind : Command a -> (a -> Command b) -> Command b

    --limit valid commands to console commands
    data ConsoleIO : Type -> Type where
        Quit : a -> ConsoleIO a
        Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

    runCmd : Command a -> IO a
    runCmd (PutStr x) = putStr x
    runCmd GetLine = getLine
    --(11.3.3)
    runCmd (Pure x) = pure x
    runCmd (Bind c f) = do res <- runCmd c
                           runCmd (f res)

    run : Count -> ConsoleIO a -> IO (Maybe a)
    run _ (Quit y) = do pure $ Just y
    run None (Do y f) = pure Nothing
    run (More x) (Do y f) = do res <- runCmd y
                               run x (f res)

namespace RunBind
    (>>=) : IO a -> (a -> Inf (RunIO b)) -> RunIO b
    (>>=) = Do

namespace CommandBind
    (>>=) : Command a -> (a -> Command b) -> Command b
    (>>=) = Bind

namespace ConsoleBind
    (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
    (>>=) = Do

greet : ConsoleIO ()
greet = do PutStr "Enter a name: "
           name <- GetLine
           if name == ""
               then do PutStr "goodbye\n"
                       Quit ()
               else do PutStr ("hello" ++ name ++ "\n")
                       greet

mutual
    correct : Stream Int -> (score : Nat) -> ConsoleIO Nat
    correct xs score = do PutStr ("Correct!" ++ "\n")
                          quiz xs (score + 1)

    wrong : Stream Int -> (answer : Int) -> (score : Nat) -> ConsoleIO Nat
    wrong xs answer score = do PutStr ("Wrong! the answer is "++show answer)
                               quiz xs score


    quiz : Stream Int -> (score : Nat) -> ConsoleIO Nat
    quiz (n1 :: n2 :: ns) score
       = do PutStr ("current score: " ++ show score ++ "\n")
            PutStr (show n1 ++ " * " ++ show n2 ++ " = ")
            answer <- GetLine
            if toLower answer == "quit" then Quit score else
                if (cast answer == n1 * n2)
                    then correct ns score
                    else wrong ns (n1 * n2) score

from : Int -> Stream Int
from x = x :: from (x+1)


disp : Maybe Nat -> String
disp Nothing = ""
disp (Just x) = cast x

namespace Exercises
    printLonger : IO ()
    printLonger
        = do putStr "first string: "
             str1 <- getLine
             putStr "second string: "
             str2 <- getLine
             print(max (length str1) (length str2))

    printLonger' : IO ()
    printLonger' = (putStr "first string: ") >>= \_ =>
                   (getLine) >>= \x =>
                   (putStr "second string: ") >>= \_ =>
                   (getLine) >>= \y =>
                   printLn (max (length x) (length y))

partial
main : IO()
main = printLonger'

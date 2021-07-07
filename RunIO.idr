-- for chapter 11.3 of Type Driven Development with Idris
--module RunIO

import MyState

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

   (>>=) : IO a -> (a -> Inf (RunIO b)) -> RunIO b
   (>>=) = Do


namespace ConsoleIO
    data Input = Answer Int
               | QuitCmd

    data Command : Type -> Type where
        PutStr : String -> Command ()
        GetLine : Command String
        --expand featureset (11.3.3)
        Pure : a -> Command a
        Bind : Command a -> (a -> Command b) -> Command b
        -- --exercise 2
        FRead : String -> Command (Either FileError String)
        FWrite : String -> String -> Command (Either FileError ())


    namespace CommandBind
        (>>=) : Command a -> (a -> Command b) -> Command b
        (>>=) = Bind
    --limit valid commands to console commands
    data ConsoleIO : Type -> Type where
        Quit : a -> ConsoleIO a
        Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b



    (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
    (>>=) = Do


    readInput : (prompt : String) -> Command Input
    readInput prompt = do PutStr prompt
                          answer <- GetLine
                          if toLower answer == "quit"
                              then Pure QuitCmd
                              else Pure $ Answer $ cast answer

    runCmd : Command a -> IO a
    runCmd (PutStr x) = putStr x
    runCmd GetLine = getLine
    --(11.3.3)
    runCmd (Pure x) = pure x
    runCmd (Bind c f) = do res <- runCmd c
                           runCmd (f res)
    runCmd (FRead x) = readFile x
    runCmd (FWrite x y) = writeFile x y

    run : Count -> ConsoleIO a -> IO (Maybe a)
    run _ (Quit y) = do pure $ Just y
    run None (Do y f) = pure Nothing
    run (More x) (Do y f) = do res <- runCmd y
                               run x (f res)

greet : ConsoleIO ()
greet = do PutStr "Enter a name: "
           name <- GetLine
           if name == ""
               then do PutStr "goodbye\n"
                       Quit ()
               else do PutStr ("hello" ++ name ++ "\n")
                       greet

namespace Exercises
    mutual                                   --exercise 1: num questions
        correct : Stream Int -> (score : Nat) -> (questions : Nat) -> ConsoleIO Nat
        correct xs score questions
            = do PutStr ("Correct!" ++ "\n")
                 quiz xs (score + 1) (questions + 1)

        wrong : Stream Int -> (answer : Int) -> (score : Nat) -> (questions : Nat) -> ConsoleIO Nat
        wrong xs answer score questions
            = do PutStr ("Wrong! the answer is " ++ show answer ++ "\n")
                 quiz xs score (questions + 1)


        quiz : Stream Int -> (score : Nat) -> (questions : Nat) -> ConsoleIO Nat
        quiz (n1 :: n2 :: ns) score questions
           = do PutStr ("current score: " ++ show score ++ "/" ++ show questions ++ "\n")
                input <- readInput (show n1 ++ " * " ++ show n2 ++ " = ")
                case input of
                      (Answer x) => if x == n1 * n2
                                        then correct ns score questions
                                        else wrong ns (n1 * n2) score questions
                      QuitCmd => Quit score

from : Int -> Stream Int
from x = x :: from (x+1)


disp : Either e String -> String
disp (Right x) = x
disp _ = ""

-- demo for exercise 2
fileOp : (path : String) -> ConsoleIO ()
fileOp path = do PutStr "\nEnter text to write to file:"
                 text <- GetLine
                 if toLower text == "quit"
                     then Quit ()
                     else do FWrite path text
                             content <- FRead path
                             PutStr (disp content)
                             fileOp path

--exercise 3
namespace Shell
    data ShellCommand = Cat String
                       | Copy String String
                       | Exit
                       | Invalid

    processInput : String -> ShellCommand
    processInput x = let args = words x in
                     case args of
                         ["exit"] => Exit
                         ["cat", name] => Cat name
                         ["copy", source, dest] => Copy source dest
                         _ => Invalid


    shell : ConsoleIO ()
    shell = do PutStr "\n:> "
               cmd <- GetLine
               case processInput cmd of
                   Exit => do PutStr "bye bye"
                              Quit ()
                   Invalid => do PutStr "Invalid Entry"
                                 shell
                   (Cat path) => do content <- FRead path
                                    PutStr ("Content of " ++ path ++ ":" ++ disp content)
                                    shell
                   (Copy src dest) => do content <- FRead src
                                         FWrite dest (disp content)
                                         shell



partial
main : IO ()
main = do run forever (shell)
          pure()

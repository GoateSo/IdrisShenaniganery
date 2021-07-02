--for chapter 11.1 and 11.2 of Type Driven Development with Idris
module InfIO

import Data.Primitives.Views
import System

%default total

data InfIO : Type where
    Do : IO a
        -> (a -> Inf InfIO)
        -> InfIO

data Count = None | More (Lazy Count)

partial
forever : Count
forever =  More forever


run : Count -> InfIO -> IO()
run (More x) (Do y f) =
    do  res <- y
        run x (f res)
run None _ = putStrLn "done"


(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

loopPrint : String -> InfIO
loopPrint x = do putStrLn x
                 loopPrint x


quiz : Stream Int -> (score : Nat) -> InfIO
quiz (n1 :: n2 :: ns) score
    = do putStrLn ("current score: " ++ show score)
         putStr (show n1 ++ " * " ++ show n2 ++ " = ")
         answer <- getLine
         if (cast answer == n1 * n2)
             then do putStrLn "Correct!"
                     quiz ns (score + 1)
             else do putStrLn "Wrong!"
                     quiz ns score


rand : Int -> Stream Int
rand seed = let seed' = 1664525 * seed + 1013904223 in
                     (seed' `shiftR` 2) :: rand seed'


inputs : Int -> Stream Int
inputs x = map bound (rand x) where
    bound : Int -> Int
    bound x with (divides x 12)
        bound ((12 * div) + rem) | (DivBy prf) = abs rem + 1

from : Int -> Stream Int
from x = x :: from (x + 1)

totalREPL : (prompt : String) -> (action : String -> String) -> InfIO
totalREPL prompt action
    = do putStr prompt
         response <- getLine
         let result = action response
         putStr result
         totalREPL prompt action

partial
main : IO()
main = do seed <- time
          run forever (quiz (inputs (fromInteger seed)) 0)

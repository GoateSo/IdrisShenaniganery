-- stack data type
-- 13.2
import Data.Vect
data StackCmd : Type -> Nat -> Nat -> Type where
    Push : Integer -> StackCmd () height (S height)
    Pop : StackCmd Integer (S height) height
    Top : StackCmd Integer (S height) (S height)

    GetStr : StackCmd String height height
    PutStr : String -> StackCmd () height height

    Pure : ty -> StackCmd ty height height
    (>>=) : StackCmd a height1 height2 ->
        (a -> StackCmd b height2 height3) ->
        StackCmd b height1 height3


data StackIO : Nat -> Type where
    Do : StackCmd t h1 h2 -> (t -> Inf (StackIO h2)) -> StackIO h1


namespace stackDo
    (>>=) : StackCmd t h1 h2 -> (t -> Inf (StackIO h2)) -> StackIO h1
    (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

runStack : (stk : Vect inSize Integer) -> StackCmd ty inSize outSize -> IO (ty, Vect outSize Integer)
runStack stk (Push x) = pure ((), (x :: stk))
runStack (x :: xs) Pop = pure (x, xs)
runStack (x :: xs) Top = pure (x, x :: xs)
runStack stk GetStr = pure (!getLine, stk)
runStack stk (PutStr x) = do putStr x
                             pure ((), stk)
runStack stk (Pure x) = pure (x, stk)
runStack stk (cmd >>= f) = do (res, stk') <- runStack stk cmd
                              runStack stk' (f res)


run : Fuel -> Vect h Integer -> StackIO h -> IO ()
run Dry stk sio = pure ()
run (More x) stk (Do cmd f) = do
    (res, stk') <- runStack stk cmd
    run x stk' (f res)

data Input = Number Integer | Add | Sub | Mul | Rem | Neg

strToInput : String -> Maybe Input
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput "mult" = Just Mul
strToInput "sub" = Just Sub
strToInput "neg" = Just Neg
strToInput "discard" = Just Rem
strToInput str = if all isDigit (unpack str)
    then Just $ Number (cast str)
    else Nothing

mutual
    tryOp : (Integer -> Integer -> Integer) -> StackIO h
    tryOp op {h = S (S a)} = do
        let c = !Pop `op` !Pop
        Push c
        PutStr (show c ++ "\n")
        stackCalc
    tryOp _ = do
        PutStr "too few items on stack\n"
        stackCalc

    tryNeg : StackIO h
    tryNeg {h = S a} = do
        let res = - !Pop
        Push res
        PutStr (show res ++ "\n")
        stackCalc
    tryNeg = do
        PutStr "too few items on stack\n"
        stackCalc

    tryRem : StackIO h
    tryRem {h = S a} = do
        Pop
        stackCalc
    tryRem = do
        PutStr "too few items on stack\n"
        stackCalc


    stackCalc : StackIO h
    stackCalc = do PutStr ">"
                   case strToInput !GetStr of
                        Nothing => do
                            PutStr "invalid input\n"
                            stackCalc
                        Just (Number x) => do
                            Push x
                            stackCalc
                        Just Rem => tryRem
                        Just Neg => tryNeg
                        Just Add => tryOp (+)
                        Just Sub => tryOp (\a, b => b - a)
                        Just Mul => tryOp (*)
main : IO()
main = run forever [] stackCalc

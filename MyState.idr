module MyState

import TreeLabel

%access public export

--chapter 12.2
|||type to describe stateful operations, from Chapter 12.2.1 Listing 12.8, akin to Control.Monad.State
data State : (stateType : Type) -> Type -> Type where
    |||get current state
    Get : State stateType stateType
    |||makes new state
    Put : stateType -> State stateType ()
    |||wraps value in state context (as value retunring state action)
    Pure : ty -> State stateType ty
    |||sequences state operations
    Bind : State stateType a -> (a -> State stateType b) -> State stateType b


get : State stateType stateType
get = Get

put : stateType -> State stateType ()
put = Put


--for Do notation purposes (monad impl later)
-- (>>=) : State s a -> (a -> State s b) -> State s b
-- (>>=) = Bind

--interface implementations
mutual
  Functor (State s) where
    map f x = pure (f !x)

  Applicative (State s) where
    pure = Pure
    f <*> a = pure (!f !a)

  Monad (State s) where
    (>>=) = Bind

|||executes a series of state actions
runState : State s a -> (st : s) -> (a, s)
runState Get st = (st, st)
runState (Put nst) st = ((), nst)
runState (Pure x) st = (x, st)
runState (Bind cmd prog) st = let (val, next) = runState cmd st in
                                  runState (prog val) next

addIfPositive : Integer -> State Integer Bool
addIfPositive x = do when (x > 0) $
                        put (!get + x)
                     pure (x > 0)

addPositives : List Integer -> State Integer Nat
addPositives xs = do added <- traverse addIfPositive xs
                     pure $ length $ filter id added

l : List String
l = ["a","b","c","d"]

condListPrint : IO ()
condListPrint = do putStr "Display? "
                   when (!getLine == "yes") $
                       do traverse putStrLn l
                          pure ()
                   putStrLn "Done"

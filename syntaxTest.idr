import Data.So

forLoop : List a -> (a -> IO ()) -> IO ()
forLoop [] f = pure ()
forLoop (x :: xs) f = do f x
                         forLoop xs f

fromTo : (from : Int) -> (to : Int) -> List Int
fromTo from to = if (from < to)
                    then from :: (fromTo (from+1) to)
                    else [from]

data Interval : Type where
   MkInterval : (lower : Double) -> (upper : Double) ->
                So (lower < upper) -> Interval

--epek scala syntax
syntax for "(" {x} "<-" [xs] ")" "{" [body] "}" = forLoop xs (\x => body)
syntax [a] "to" [b] = fromTo a b


syntax dont [a] = do a

main : IO ()
main = dont printLn True

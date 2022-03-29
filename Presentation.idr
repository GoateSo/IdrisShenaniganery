fibs : List Int
fibs = [1,1,2,3,5,8,13]

ones : List Int
ones = [1..9]

odds : List Int
odds = [1,3..10]

f : Int -> List Int
f x = [x,x+1]

flatMap : Monad m => (a -> m b) -> m a -> m b
flatMap f m = m >>= f

helper : (a -> Bool) -> a -> List a
helper p x = if p x then [x] else []

-- filter : (a -> Bool) -> List a -> List a
-- filter p xs = flatMap (helper p) xs
-- *Presentation> only (>5) [1..10]
-- [6, 7, 8, 9, 10] : List Integer
-- *Presentation> map (+2) (Just 2)
-- Just 4 : Maybe Integer
-- *Presentation> map (+2) Nothing
-- Nothing : Maybe Integer

main : IO ()
main = flatMap (putStrLn) 
       getLine

flatMap : (String -> IO ()) -> IO String -> IO ()
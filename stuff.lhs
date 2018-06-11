> module E3 where
>
> import Data.Char
> import Data.List


Exercise 3.1 OK
------------

Suppose we want to have unordered pairs, for which $(4,5) == (5,4)$.
For example, think about a round of a game with two players.
This is an exercise to define instances of the `Show` and `Eq` type classes.

> data UnOrdPair a = UOP (a,a)

Implement a `Show` and an `Eq` instance such that we get:

    > show (UOP (1,4))
    UOP (1,4)
    > show (UOP (4,1))
    UOP (1,4)
    > UOP (1,4) == UOP (4,1)
    True

> instance (Show a, Ord a) => Show (UnOrdPair a) where
>   show (UOP (x,y)) | x >= y     = "UOP " ++ show (y,x)
>                    | otherwise  = "UOP " ++ show (x,y)


Hint: start by distinguishing whether we have `x < y` or not.

> instance Ord a => Eq (UnOrdPair a) where
>   (==) (UOP (x1,y1)) (UOP (x2,y2)) | x1 == x2 && y1 == y2    = True
>                                    | x1 == y2 && y1 == x2    = True
>                                    | otherwise               = False

GUard also unnecessary here!
Hint: Use || and describe the two cases in which the pairs should be equal.


Exercise 3.2 OK
------------

Consider Hello World 2.0 from the lectures:

> dialogue :: IO ()
> dialogue = do
>   putStrLn "Hello! Who are you?"
>   name <- getLine
>   putStrLn $ "Nice to meet you, " ++ name ++ "!"
>   putStrLn "How old are you?"
>   ageString <- getLine
>   let age = read ageString :: Int
>   putStrLn $ "Ah, that is " ++ show (100 - age) ++ " years younger than me!"

   let age = read ageString :: Int
   let dif = 100 - age ::Int

Extend this implementation such that it behaves like this:

    E3> dialogue
    Hello! Who are you?
    Bob -- user input
    Nice to meet you, Bob!
    How old are you?
    94 -- user input
    Ah, that is 6 years younger than me!

Hint: You might want a line like `let age = read ageString :: Int`.

> module Sudoku where
>
> import Data.Char
> import Data.List
> import System.Random

> type Row    = Int
> type Column = Int
> type Value  = Int
> type Grid   = [[Value]]

Exercise 3: this code adapts the code for a Sudoku solver/generator to that for a
binary puzzle:
Each cell should contain a zero or a one.
No more than two similar numbers below or next to each other are allowed.
Each row and each column is unique and contains as many zeros as ones.

OLD CODE START:

> positions, values :: [Int]
> positions = [1..10]
> values    = [0,1]

2 represents a blank slot:

> showVal :: Value -> String
> showVal 2 = " "
> showVal d = show d


> showRow :: [Value] -> IO()
> showRow [a1,a2,a3,a4,a5,a6,a7,a8,a9,a10] =
>  do  putChar '|'         ; putChar ' '
>      putStr (showVal a1) ; putChar ' '
>      putStr (showVal a2) ; putChar ' '
>      putStr (showVal a3) ; putChar ' '
>      putStr (showVal a4) ; putChar ' '
>      putStr (showVal a5) ; putChar ' '
>      putChar '|'         ; putChar ' '
>      putStr (showVal a6) ; putChar ' '
>      putStr (showVal a7) ; putChar ' '
>      putStr (showVal a8) ; putChar ' '
>      putStr (showVal a9) ; putChar ' '
>      putStr (showVal a10) ; putChar ' '
>      putChar '|'         ; putChar '\n'


> showGrid :: Grid -> IO()
> showGrid [as,bs,cs,ds,es,fs,gs,hs,is,js] =
>  do putStrLn ("+-------+-------+-------+")
>     showRow as; showRow bs; showRow cs; showRow ds; showRow es
>     putStrLn ("+-------+-------+-------+")
>     showRow fs; showRow gs; showRow hs; showRow is; showRow js
>     putStrLn ("+-------+-------+-------+")


> type Binary = (Row,Column) -> Value

> bin2grid :: Binary -> Grid
> bin2grid s =
>   [ [ s (r,c) | c <- [1..10] ] | r <- [1..10] ]
>
> grid2bin :: Grid -> Binary
> grid2bin gr = \ (r,c) -> pos gr (r,c)
>   where
>   pos :: [[a]] -> (Row,Column) -> a
>   pos gr (r,c) = (gr !! (r-1)) !! (c-1)

> showBinary :: Binary -> IO()
> showBinary = showGrid . bin2grid

Free values are available values at open slot positions. Free in a sequence are all values that haven't been used yet:

> freeInSeq :: [Value] -> [Value]
> freeInSeq seq | 0 `elem` ([0,0,0,0,0,1,1,1,1,1] \\ seq) && 1 `elem` ([0,0,0,0,0,1,1,1,1,1] \\ seq)          = [0,1]
>               | 0 `elem` ([0,0,0,0,0,1,1,1,1,1] \\ seq) && not (1 `elem` ([0,0,0,0,0,1,1,1,1,1] \\ seq))    = [0]
>               | not (0 `elem` ([0,0,0,0,0,1,1,1,1,1] \\ seq)) && 1 `elem` ([0,0,0,0,0,1,1,1,1,1] \\ seq)    = [1]
>               | otherwise                                                                                   = []

> freeInRow :: Binary -> Row -> [Value]
> freeInRow s r =
>   freeInSeq [ s (r,i) | i <- positions  ]

> freeInColumn :: Binary -> Column -> [Value]
> freeInColumn s c =
>   freeInSeq [ s (i,c) | i <- positions ]

Check positions to the left and right in row and column; for this, four different cases have to be
distinguished. The freeAtPos function works when applied directly to example1.

> freeColumnDouble :: Binary -> (Row, Column) -> [Value]
> freeColumnDouble s (r,c) | r > 2 && (s (r-1, c) == s (r-2, c))         = [0,1] \\ [s (r-1, c)]
>                          | r < 9 && (s (r+1, c) == s (r+2, c))         = [0,1] \\ [s (r+1, c)]
>                          | r < 10 && r > 1 && s (r-1, c) == s (r+1, c) = [0,1] \\ [s (r-1, c)]
>                          | otherwise                                   = [0,1]

> freeRowDouble :: Binary -> (Row, Column) -> [Value]
> freeRowDouble s (r,c) | c > 2 && (s (r, c-1) == s (r, c-2))            = [0,1] \\ [s (r, c-1)]
>                       | c < 9 && (s (r, c+1) == s (r, c+2))            = [0,1] \\ [s (r, c+1)]
>                       | c < 10 && c > 1 && (s (r, c-1) == s (r, c+1))  = [0,1] \\ [s (r, c-1)]
>                       | otherwise                                      = [0,1]

> freeAtPos :: Binary -> (Row,Column) -> [Value]
> freeAtPos s (r,c) = (freeInRow s r)
>    `intersect` (freeInColumn s c)
>    `intersect` (freeColumnDouble s (r,c))
>    `intersect` (freeRowDouble s (r,c))

injective :: Eq a => [a] -> Bool; is change correct?

> injective :: [Int] -> Bool
> injective xs = (xs \\ [0,0,0,0,0,1,1,1,1,1]) == []

> rowInjective :: Binary -> Row -> Bool
> rowInjective s r = injective vs where
>    vs = filter (/= 0) [ s (r,i) | i <- positions ]

> colInjective :: Binary -> Column -> Bool
> colInjective s c = injective vs where
>    vs = filter (/= 0) [ s (i,c) | i <- positions ]

> consistent :: Binary -> Bool
> consistent s = and $
>                [ rowInjective s r |  r <- positions ]
>                 ++
>                [ colInjective s c |  c <- positions ]

> extend :: Binary -> ((Row,Column),Value) -> Binary
> extend = update

> update :: Eq a => (a -> b) -> (a,b) -> a -> b
> update f (y,z) x = if x == y then z else f x

> type Constraint = (Row,Column,[Value])

> type Node = (Binary,[Constraint])
>
> showNode :: Node -> IO()
> showNode = showBinary . fst

> solved  :: Node -> Bool
> solved = null . snd

> extendNode :: Node -> Constraint -> [Node]
> extendNode (s,constraints) (r,c,vs) =
>    [(extend s ((r,c),v),
>      sortBy length3rd $
>          prune (r,c,v) constraints) | v <- vs ]

> length3rd :: (a,b,[c]) -> (a,b,[c]) -> Ordering
> length3rd (_,_,zs) (_,_,zs') = compare (length zs) (length zs')


CHANGE PRUNE

> prune :: (Row,Column,Value)
>       -> [Constraint] -> [Constraint]
> prune _ [] = []
> prune (r,c,v) ((x,y,zs):rest)
>   | r == x = (x,y,zs\\[v]) : prune (r,c,v) rest
>   | c == y = (x,y,zs\\[v]) : prune (r,c,v) rest

   | sameblock (r,c) (x,y) =
         (x,y,zs\\[v]) : prune (r,c,v) rest

>   | otherwise = (x,y,zs) : prune (r,c,v) rest


> initNode :: Grid -> [Node]
> initNode gr = let s = grid2bin gr in
>               if (not . consistent) s then []
>               else [(s, constraints s)]

> openPositions :: Binary -> [(Row,Column)]
> openPositions s = [ (r,c) | r <- positions,
>                             c <- positions,
>                             s (r,c) == 2 ]

> constraints :: Binary -> [Constraint]
> constraints s = sortBy length3rd
>     [(r,c, freeAtPos s (r,c)) |
>                        (r,c) <- openPositions s ]

> search :: (node -> [node])
>        -> (node -> Bool) -> [node] -> [node]
> search children goal [] = []
> search children goal (x:xs)
>   | goal x    = x : search children goal xs
>   | otherwise = search children goal ((children x) ++ xs)

> solveNs :: [Node] -> [Node]
> solveNs = search succNode solved
>
> succNode :: Node -> [Node]
> succNode (s,[]) = []
> succNode (s,p:ps) = extendNode (s,ps) p

> solveAndShow :: Grid -> IO[()]
> solveAndShow gr = solveShowNs (initNode gr)
>
> solveShowNs :: [Node] -> IO[()]
> solveShowNs = sequence . fmap showNode . solveNs

> example1 :: Grid
> example1 = [[2,2,2,2,2,2,2,1,2,2],
>             [2,0,0,2,2,0,2,2,1,2],
>             [2,0,2,2,1,2,2,0,2,0],
>             [2,2,1,2,2,2,1,2,2,2],
>             [1,2,1,2,2,2,2,2,2,1],
>             [2,2,2,2,2,2,2,1,2,2],
>             [2,0,2,2,1,2,2,2,0,2],
>             [2,2,2,2,1,1,2,2,2,0],
>             [2,0,2,0,2,2,1,2,2,0],
>             [0,2,2,2,0,2,2,2,1,2]]

> example2 :: Grid
> example2 = [[1,2,0,0,2,2,2,2,2,2],
>             [2,0,0,2,2,1,2,0,0,2],
>             [2,2,2,2,0,2,2,2,0,2],
>             [2,0,2,2,2,2,0,2,2,2],
>             [2,2,1,2,2,2,2,2,2,0],
>             [1,2,2,0,2,2,2,2,2,2],
>             [2,2,2,2,1,2,1,2,0,2],
>             [2,2,2,2,1,2,2,0,0,2],
>             [2,1,1,2,2,2,2,2,2,2],
>             [0,0,2,1,2,2,0,0,2,1]]


OLD CODE END

> emptyN :: Node
> emptyN = (\ _ -> 0,constraints (\ _ -> 0))

> getRandomInt :: Int -> IO Int
> getRandomInt n = getStdRandom (randomR (0,n))

> getRandomItem :: [a] -> IO [a]
> getRandomItem [] = return []
> getRandomItem xs = do n <- getRandomInt maxi
>                       return [xs !! n]
>                    where maxi = length xs - 1

> randomize :: Eq a => [a] -> IO [a]
> randomize xs = do y <- getRandomItem xs
>                   if null y
>                     then return []
>                     else do ys <- randomize (xs\\y)
>                             return (head y:ys)

> sameLen :: Constraint -> Constraint -> Bool
> sameLen (_,_,xs) (_,_,ys) = length xs == length ys

> getRandomCnstr :: [Constraint] -> IO [Constraint]
> getRandomCnstr cs = getRandomItem (f cs)
>   where f [] = []
>         f (x:xs) = takeWhile (sameLen x) (x:xs)

> rsuccNode :: Node -> IO [Node]
> rsuccNode (s,cs) = do xs <- getRandomCnstr cs
>                       if null xs
>                         then return []
>                         else return
>                           (extendNode (s,cs\\xs) (head xs))

> rsolveNs :: [Node] -> IO [Node]
> rsolveNs ns = rsearch rsuccNode solved (return ns)

> rsearch :: (node -> IO [node])
>             -> (node -> Bool) -> IO [node] -> IO [node]
> rsearch succ goal ionodes =
>   do xs <- ionodes
>      if null xs
>        then return []
>        else
>          if goal (head xs)
>            then return [head xs]
>            else do ys <- rsearch succ goal (succ (head xs))
>                    if (not . null) ys
>                       then return [head ys]
>                       else if null (tail xs) then return []
>                            else
>                              rsearch
>                                succ goal (return $ tail xs)

> genRandomBinary :: IO Node
> genRandomBinary = do [r] <- rsolveNs [emptyN]
>                      return r

> randomS = genRandomBinary >>= showNode

> uniqueSol :: Node -> Bool
> uniqueSol node = singleton (solveNs [node]) where
>   singleton [] = False
>   singleton [x] = True
>   singleton (x:y:zs) = False

> eraseS :: Binary -> (Row,Column) -> Binary
> eraseS s (r,c) (x,y) | (r,c) == (x,y) = 0
>                      | otherwise      = s (x,y)

> eraseN :: Node -> (Row,Column) -> Node
> eraseN n (r,c) = (s, constraints s)
>   where s = eraseS (fst n) (r,c)

> minimalize :: Node -> [(Row,Column)] -> Node
> minimalize n [] = n
> minimalize n ((r,c):rcs) | uniqueSol n' = minimalize n' rcs
>                          | otherwise    = minimalize n  rcs
>   where n' = eraseN n (r,c)

> filledPositions :: Binary -> [(Row,Column)]
> filledPositions s = [ (r,c) | r <- positions,
>                               c <- positions, s (r,c) /= 0 ]

> genProblem :: Node -> IO Node
> genProblem n = do ys <- randomize xs
>                   return (minimalize n ys)
>    where xs = filledPositions (fst n)

> main :: IO ()
> main = do [r] <- rsolveNs [emptyN]
>           showNode r
>           s  <- genProblem r
>           showNode s

> module Sudoku where
>
> import Data.Char
> import Data.List
> import System.Random
> import Debug.Trace

The following code integrates the code for solving Sudokus for different types
of Sudokus: the usual type, a type with four additional 3x3 blocks with left-top
corners (2,2), (2,6), (6,2), and (6,6), and a type where the diagonals require
an injective function from 1-9.

To Do:
However, a better indicator for "how hard" a Sudoku is might be to keep
track of the search process (which you can also think of as a tree). To
do that, you could add counters to the recursive functions, so that we
know how many steps of reasoning or how many tries the program needed
before it found a solution.

> type Row    = Int
> type Column = Int
> type Value  = Int
> type Grid   = [[Value]]
>
> positions, values :: [Int]
> positions = [1..9]
> values    = [1..9]
>
> blocks :: [[Int]]
> blocks = [[1..3],[4..6],[7..9]]

0 represents a blank slot:

> showVal :: Value -> String
> showVal 0 = " "
> showVal d = show d

> showRow :: [Value] -> IO()
> showRow [a1,a2,a3,a4,a5,a6,a7,a8,a9] =
>  do  putChar '|'         ; putChar ' '
>      putStr (showVal a1) ; putChar ' '
>      putStr (showVal a2) ; putChar ' '
>      putStr (showVal a3) ; putChar ' '
>      putChar '|'         ; putChar ' '
>      putStr (showVal a4) ; putChar ' '
>      putStr (showVal a5) ; putChar ' '
>      putStr (showVal a6) ; putChar ' '
>      putChar '|'         ; putChar ' '
>      putStr (showVal a7) ; putChar ' '
>      putStr (showVal a8) ; putChar ' '
>      putStr (showVal a9) ; putChar ' '
>      putChar '|'         ; putChar '\n'

> showGrid :: Grid -> IO()
> showGrid [as,bs,cs,ds,es,fs,gs,hs,is] =
>  do putStrLn ("+-------+-------+-------+")
>     showRow as; showRow bs; showRow cs
>     putStrLn ("+-------+-------+-------+")
>     showRow ds; showRow es; showRow fs
>     putStrLn ("+-------+-------+-------+")
>     showRow gs; showRow hs; showRow is
>     putStrLn ("+-------+-------+-------+")

> type Sudoku = (Row,Column) -> Value

> sud2grid :: Sudoku -> Grid
> sud2grid s =
>   [ [ s (r,c) | c <- [1..9] ] | r <- [1..9] ]
>
> grid2sud :: Grid -> Sudoku
> grid2sud gr = \ (r,c) -> pos gr (r,c)
>   where
>   pos :: [[a]] -> (Row,Column) -> a
>   pos gr (r,c) = (gr !! (r-1)) !! (c-1)

> showSudoku :: Sudoku -> IO()
> showSudoku = showGrid . sud2grid

Picking the block of a position:

> bl :: Int -> [Int]
> bl x = concat $ filter (elem x) blocks

For the Sudoku with the four extra 3x3 blocks, we define additional blocks:

> addblocks :: [[Int]]
> addblocks = [[2..4],[6..8]]

> addbl :: Int -> [Int]
> addbl x = concat $ filter (elem x) addblocks

We now define restrictions that distinguish between different parts of the
Sudoku that require injectivity. `Restriction' gives all coordinates of a certain
restriction.

> type Restriction = (Row,Column) -> [(Row,Column)]

RemainingValues gives you list of all values in that restriction.

> allValues :: Restriction -> Sudoku -> (Row, Column) -> [Value]
> allValues res s (r,c) = map s (res (r,c))

> row :: Restriction
> row (r,_) = [(r, c') | c' <- positions]

> column :: Restriction
> column (_, c) = [ (r', c) | r' <- positions]

> subGrid :: Restriction
> subGrid (r, c) = [ (r', c') | r' <- bl r, c' <- bl c]

> diagonalUp :: Restriction
> diagonalUp (r, c) = [ (r',c') | r' <- positions, c' <- positions, (r' + c') == 10, (r + c) == 10 ]

> diagonalDown :: Restriction
> diagonalDown (r,c) = [ (r',c') | r' <- positions, c' <- positions, r' == c', r == c]

> addsubGrid :: Restriction
> addsubGrid (r,c) = [ (r', c') | r' <- addbl r, c' <- addbl c ]

> allRestrictions = [row, column, subGrid, diagonalUp, diagonalDown, addsubGrid]

Free values are available values at open slot positions. We define the free values for
every restriction:

> freeInSeq :: [Value] -> [Value]
> freeInSeq sequ = values \\ sequ

New freeAtPos (foldr1 takes two elements out of the list, applies intersect, and then intersects that with the next element, etc):
freeInSeq still needs to be applied to remainingValues!

> freeAtPos :: [Restriction] -> Sudoku -> (Row,Column) -> [Value]
> freeAtPos x s (r,c) = foldr1 intersect [ freeInSeq (allValues res s (r,c)) | res <- x ]

The injectivity checks also allow for choosing a restriction:

> injective :: Eq a => [a] -> Bool
> injective xs = nub xs == xs

> injectiveFor :: Restriction -> Sudoku -> (Row, Column) -> Bool
> injectiveFor x s (r,c) = injective vs where
>    vs = filter (/= 0) (map s $ x (r, c)) -- TODO think about this!

Consistency checks for injectivity for every restriction:

> consistent :: [Restriction] -> Sudoku -> Bool
> consistent x s =
>    not (False `elem` [ injectiveFor res s (r,c) | res <- x, r <- positions, c <- positions])

> extend :: Sudoku -> ((Row,Column),Value) -> Sudoku
> extend = update

> update :: Eq a => (a -> b) -> (a,b) -> a -> b
> update f (y,z) x = if x == y then z else f x

> type Constraint = (Row,Column,[Value])

> type Node = (Sudoku,[Constraint])
>
> showNode :: Node -> IO()
> showNode = showSudoku . fst

> solved  :: Node -> Bool
> solved = null . snd

> extendNode :: [Restriction] -> Node -> Constraint -> [Node]
> extendNode us (s,constr) (r,c,vs) =
>    [(extend s ((r,c),v),
>      sortBy length3rd $
>          prune us (r,c,v) constr) | v <- vs ]

> length3rd :: (a,b,[c]) -> (a,b,[c]) -> Ordering
> length3rd (_,_,zs) (_,_,zs') = compare (length zs) (length zs')

> prune :: [Restriction] -> (Row,Column,Value)
>       -> [Constraint] -> [Constraint]
> prune _  _ [] = []
> prune us (r,c,v) ((x,y,zs):rest)
>   | r == x = (x,y,zs\\[v]) : prune us (r,c,v) rest
>   | c == y = (x,y,zs\\[v]) : prune us (r,c,v) rest
>   | same us (r,c) (x,y) =
>         (x,y,zs\\[v]) : prune us (r,c,v) rest
>   | otherwise = (x,y,zs) : prune us (r,c,v) rest

The sameblock function should return True when a position is in the same subgrid,
and optionally in the same diagonal and additional subgrid. Right now it will always return
True when it is in the same diagonal and additional subgrid (even if it is a normal Sudoku).

OLD CODE--
 sameblocknormal :: (Row,Column) -> (Row,Column) -> Bool
 sameblocknormal (r,c) (x,y) = (bl r == bl x) && (bl c == bl y)

 sameblockdiag :: (Row,Column) -> (Row,Column) -> Bool
 sameblockdiag (r,c) (x,y) | (bl r == bl x) && (bl c == bl y)                             = True
                           | (r == c && x == y) || ((r + c == 10) && (x + y == 10))       = True
                           | otherwise                                                    = False

 sameblockadd :: (Row,Column) -> (Row,Column) -> Bool
 sameblockadd (r,c) (x,y) | (bl r == bl x) && (bl c == bl y)                             = True
                          | (addbl r == addbl x) && (addbl c == addbl y)                 = True
                          | otherwise                                                    = False
--

Addition sameFor: cannot be empty list as otherwise e.g. coordinates that are both not in
either diagonal are considered to be in a same block.

> sameFor :: Restriction -> (Row,Column) -> (Row,Column) -> Bool
> sameFor u (r,c) (x,y) = (u (r,c) == u (x,y)) && not (u (r, c) == [])

> same :: [Restriction] -> (Row,Column) -> (Row,Column) -> Bool
> same us (r,c) (x,y) = or [ sameFor u (r,c) (x,y) | u <- us ]

> initNode :: Grid -> [Restriction] -> [Node]
> initNode gr x = let s = grid2sud gr in
>               if not (consistent x s) then []
>               else [(s, constraints s x)]

-- old code:               if (not . consistent) s then []

> openPositions :: Sudoku -> [(Row,Column)]
> openPositions s = [ (r,c) | r <- positions,
>                             c <- positions,
>                             s (r,c) == 0 ]

> constraints :: Sudoku -> [Restriction] -> [Constraint]
> constraints s x = sortBy length3rd
>     [(r,c, freeAtPos x s (r,c)) |
>                        (r,c) <- openPositions s ]

> search :: (node -> [node])
>        -> (node -> Bool) -> [node] -> [node]
> search children goal [] = []
> search children goal (x:xs)
>   | goal x    = x : search children goal xs
>   | otherwise = search children goal ((children x) ++ xs)

> solveNs :: [Restriction] -> [Node] -> [Node]
> solveNs us = search (succNode us) solved
>
> succNode :: [Restriction] -> Node -> [Node]
> succNode us (s,[]) = []
> succNode us (s,p:ps) = extendNode us (s,ps) p

> solveAndShow :: Grid -> [Restriction] -> IO[()]
> solveAndShow gr x = solveShowNs x (initNode gr x)

solveAndShow should be adapted into a function that takes into account the type of Sudoku.

> solveShowNs :: [Restriction] -> [Node] -> IO[()]
> solveShowNs us = sequence . fmap showNode . (solveNs us)

We define the following lists of restrictions to make it shorter:

> normal :: [Restriction]
> normal = [row, column, subGrid]

> diagonal :: [Restriction]
> diagonal = [row, column, subGrid, diagonalUp, diagonalDown]

> addGrid :: [Restriction]
> addGrid = [row, column, subGrid, addsubGrid]

> examplenormal :: Grid
> examplenormal = [[5,3,0,0,7,0,0,0,0],
>                  [6,0,0,1,9,5,0,0,0],
>                  [0,9,8,0,0,0,0,6,0],
>                  [8,0,0,0,6,0,0,0,3],
>                  [4,0,0,8,0,3,0,0,1],
>                  [7,0,0,0,2,0,0,0,6],
>                  [0,6,0,0,0,0,2,8,0],
>                  [0,0,0,4,1,9,0,0,5],
>                  [0,0,0,0,8,0,0,7,9]]

> examplediag :: Grid
> examplediag = [[0,0,0,0,0,0,0,4,0],
>                [4,0,0,9,8,0,0,0,6],
>                [0,3,0,0,0,7,9,8,0],
>                [0,0,0,0,0,0,0,0,0],
>                [0,0,5,7,0,4,1,0,0],
>                [0,0,0,0,0,0,0,0,0],
>                [0,6,3,8,0,0,0,5,0],
>                [8,0,0,0,2,6,0,0,3],
>                [0,1,0,0,0,0,0,0,0]]

> exampleadd :: Grid
> exampleadd = [[0,0,2,0,0,0,0,0,0],
>              [0,0,4,0,8,0,9,0,0],
>              [0,0,0,3,0,0,0,0,0],
>              [0,0,0,0,0,5,4,0,1],
>              [0,0,0,0,0,0,0,0,0],
>              [5,0,0,2,0,0,0,0,8],
>              [0,0,0,0,0,6,0,7,0],
>              [0,5,0,0,0,0,0,0,0],
>              [0,0,0,0,3,0,0,1,0]]

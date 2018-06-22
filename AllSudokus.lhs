> module Sudoku where
>
> import Data.Char
> import Data.List
> import System.Random

The following code integrates the code for solving Sudokus for different types
of Sudokus: the usual type, a type with four additional 3x3 blocks with left-top
corners (2,2), (2,6), (6,2), and (6,6), and a type where the diagonals require
an injective function from 1-9.

I still want to implement an extra input argument in solveAndShow that clarifies what type
of Sudoku it is that needs to be solved, so that the right functions can be used.

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
Sudoku that require injectivity.

> -- type Restriction = [(Row,Column)]

> type Restriction = Sudoku -> (Row, Column) -> [Value]

> row :: Restriction
> row s (r,_) = [s (r, c') | c' <- positions]

> column :: Restriction
> column s (_, c) = [s (r', c) | r' <- positions]

> subGrid :: Restriction
> subGrid s (r, c) = [ s (r', c') | r' <- bl r, c' <- bl c]

> diagonalUp :: Restriction
> diagonalUp s (r, c) = [ s (r',c') | r' <- positions, c' <- positions, (r' + c') == 10, (r + c) == 10 ]

> diagonalDown :: Restriction
> diagonalDown s (r,c) = [ s (r',c') | r' <- positions, c' <- positions, r' == c', r == c]

> addsubGrid :: Restriction
> addsubGrid s (r,c) = [ s (r', c') | r' <- addbl r, c' <- addbl c ]

> allRestrictions = [row, column, subGrid, diagonalUp, diagonalDown, addsubGrid]

Free values are available values at open slot positions. We define the free values for
every restriction:

> -- freeIn :: Restriction -> Sudoku -> [Value]

> freeInSeq :: [Value] -> [Value]
> freeInSeq sequ = values \\ sequ

freeIn lets you select the type of restriction that you want:

> freeIn :: Restriction -> Sudoku -> (Row, Column) -> [Value]
> freeIn x s (r,c) = freeInSeq (x s (r,c))

> -- freeInSeq = freeIn (row (r,c))

The freeAtPos definition should be made more concise, e.g. with map, only I couldn't
figure out how to implement `intersect` then:

> freeAtPos :: Sudoku -> (Row,Column) -> [Value]
> freeAtPos s (r,c) = freeIn row s (r,c)
>                         `intersect` freeIn column s (r,c)
>                         `intersect` freeIn subGrid s (r,c)
>                         `intersect` freeIn diagonalUp s (r,c)
>                         `intersect` freeIn diagonalDown s (r,c)
>                         `intersect` freeIn addsubGrid s (r,c)

The injectivity checks also allow for choosing a restriction:

> injective :: Eq a => [a] -> Bool
> injective xs = nub xs == xs

> injectiveFor :: Restriction -> Sudoku -> (Row, Column) -> Bool
> injectiveFor x s (r,c) = injective vs where
>    vs = filter (/= 0) (x s (r, c))

Consistency checks for injectivity for every restriction:

> consistent :: Sudoku -> Bool
> consistent s =
>    not (False `elem` [ injectiveFor res s (r,c) | res <- allRestrictions, r <- positions, c <- positions])

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

> extendNode :: Node -> Constraint -> [Node]
> extendNode (s,constr) (r,c,vs) =
>    [(extend s ((r,c),v),
>      sortBy length3rd $
>          prune (r,c,v) constr) | v <- vs ]

> length3rd :: (a,b,[c]) -> (a,b,[c]) -> Ordering
> length3rd (_,_,zs) (_,_,zs') = compare (length zs) (length zs')

> prune :: (Row,Column,Value)
>       -> [Constraint] -> [Constraint]
> prune _ [] = []
> prune (r,c,v) ((x,y,zs):rest)
>   | r == x = (x,y,zs\\[v]) : prune (r,c,v) rest
>   | c == y = (x,y,zs\\[v]) : prune (r,c,v) rest
>   | sameblock (r,c) (x,y) =
>         (x,y,zs\\[v]) : prune (r,c,v) rest
>   | otherwise = (x,y,zs) : prune (r,c,v) rest

The sameblock function should return True when a position is in the same subgrid,
and optionally in the same diagonal and additional subgrid. Right now it will always return
True when it is in the same diagonal and additional subgrid (even if it is a normal Sudoku).

> sameblock :: (Row,Column) -> (Row,Column) -> Bool
> sameblock (r,c) (x,y) | (bl r == bl x) && (bl c == bl y)                             = True
>                       | (r == c && x == y) || ((r + c == 10) && (x + y == 10))       = True
>                       | (addbl r == addbl x) && (addbl c == addbl y)                 = True
>                       | otherwise                                                    = False

> initNode :: Grid -> [Node]
> initNode gr = let s = grid2sud gr in
>               if (not . consistent) s then []
>               else [(s, constraints s)]

> openPositions :: Sudoku -> [(Row,Column)]
> openPositions s = [ (r,c) | r <- positions,
>                             c <- positions,
>                             s (r,c) == 0 ]

> constraints :: Sudoku -> [Constraint]
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

solveAndShow should be adapted into a function that takes into account the type of Sudoku.

> solveShowNs :: [Node] -> IO[()]
> solveShowNs = sequence . fmap showNode . solveNs

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

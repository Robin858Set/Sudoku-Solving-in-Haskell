> module Sudoku where
>
> import Data.Char
> import Data.List
> import System.Random

The following code adapts the already existing code into a sudoku solver that also requires
that each of the two diagonals also yield a surjective function.

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

> subGrid :: Sudoku -> (Row,Column) -> [Value]
> subGrid s (r,c) =
>   [ s (r',c') | r' <- bl r, c' <- bl c ]

> diagonalUp :: Sudoku -> (Row, Column) -> [Value]
> diagonalUp s (r,c) =
>   [ s (r',c') | r' <- positions, c' <- positions, (r' + c') == 10, (r + c) == 10 ]

> diagonalDown :: Sudoku -> (Row, Column) -> [Value]
> diagonalDown s (r,c) =
>   [ s (r',c') | r' <- positions, c' <- positions, r' == c', r == c]

Free values are available values at open slot positions. Free in a sequence are all values that haven't been used yet:

> type Restriction = [(Row,Column)]
>
> row :: (Row,Column) -> Restriction
> row (r,_) = [(r,c') | c' <- positions]

> -- allRestrictions = [row,column,subgrid,diagonalUp,diagonalDown]

> freeIn :: Restriction -> Sudoku -> [Value]
> freeIn = undefined

> freeInSeq :: [Value] -> [Value]
> freeInSeq sequ = values \\ sequ

> freeInRow :: Sudoku -> Row -> [Value]
> freeInRow s r =
>   freeInSeq [ s (r,i) | i <- positions  ]

> -- freeInSeq = freeIn (row (r,c))

> freeInColumn :: Sudoku -> Column -> [Value]
> freeInColumn s c =
>   freeInSeq [ s (i,c) | i <- positions ]

> freeInSubgrid :: Sudoku -> (Row,Column) -> [Value]
> freeInSubgrid s (r,c) = freeInSeq (subGrid s (r,c))

> freeInDiagonalUp :: Sudoku -> (Row, Column) -> [Value]
> freeInDiagonalUp s (r,c) = freeInSeq (diagonalUp s (r,c))

> freeInDiagonalDown :: Sudoku -> (Row, Column) -> [Value]
> freeInDiagonalDown s (r,c) = freeInSeq (diagonalDown s (r,c))

> freeAtPos :: Sudoku -> (Row,Column) -> [Value]
> freeAtPos s (r,c) =
>   (freeInRow s r)
>    `intersect` (freeInColumn s c)
>    `intersect` (freeInSubgrid s (r,c))
>    `intersect` (freeInDiagonalUp s (r,c))
>    `intersect` (freeInDiagonalDown s (r,c))

> injectiveFor :: Restriction -> Sudoku -> Bool
> injectiveFor = undefined

> injective :: Eq a => [a] -> Bool
> injective xs = nub xs == xs

> rowInjective :: Sudoku -> Row -> Bool
> rowInjective s r = injective vs where
>    vs = filter (/= 0) [ s (r,i) | i <- positions ]

> colInjective :: Sudoku -> Column -> Bool
> colInjective s c = injective vs where
>    vs = filter (/= 0) [ s (i,c) | i <- positions ]

> subgridInjective :: Sudoku -> (Row,Column) -> Bool
> subgridInjective s (r,c) = injective vs where
>    vs = filter (/= 0) (subGrid s (r,c))

> diagonalUpInjective :: Sudoku -> (Row, Column) -> Bool
> diagonalUpInjective s (r,c) = injective vs where
>   vs = filter (/= 0) (diagonalUp s (r,c))

> diagonalDownInjective :: Sudoku -> (Row, Column) -> Bool
> diagonalDownInjective s (r,c) = injective vs where
>   vs = filter (/= 0) (diagonalDown s (r,c))

> consistent :: Sudoku -> Bool
> consistent s = and $ -- [ injectiveFor res | res <- allRestrictions ]
>                [ rowInjective s r |  r <- positions ]
>                 ++
>                [ colInjective s c |  c <- positions ]
>                 ++
>                [ subgridInjective s (r,c) |
>                     r <- [1,4,7], c <- [1,4,7]]
>                 ++
>                [ diagonalUpInjective s (r,c) |
>                     r <- [9], c <- [1] ]
>                 ++
>                [ diagonalDownInjective s (r,c) |
>                     r <- [1], c <- [1] ]

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
>
> sameblock :: (Row,Column) -> (Row,Column) -> Bool
> sameblock (r,c) (x,y) | (bl r == bl x) && (bl c == bl y)                             = True
>                       | (r == c && x == y) || ((r + c == 10) && (x + y == 10))       = True
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
>
> solveShowNs :: [Node] -> IO[()]
> solveShowNs = sequence . fmap showNode . solveNs

> example1 :: Grid
> example1 = [[5,3,0,0,7,0,0,0,0],
>             [6,0,0,1,9,5,0,0,0],
>             [0,9,8,0,0,0,0,6,0],
>             [8,0,0,0,6,0,0,0,3],
>             [4,0,0,8,0,3,0,0,1],
>             [7,0,0,0,2,0,0,0,6],
>             [0,6,0,0,0,0,2,8,0],
>             [0,0,0,4,1,9,0,0,5],
>             [0,0,0,0,8,0,0,7,9]]

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

\section*{Code Sudoku Solving}

The following code integrates the code for solving and generating Sudokus for
different types of Sudokus: the usual type, a type with four additional 3x3
blocks with left-top corners (2,2), (2,6), (6,2), and (6,6), and a type where
the diagonals require a one-to-one function from 1-9.

\begin{code}
module Sudoku where
\end{code}
\begin{code}
import Data.List
import System.Random
\end{code}

\subsection*{Defining a Sudoku}
The following code defines the basic types that are needed to compose a Sudoku
and implements a function that prints a Sudoku the way we know it.

\begin{code}
type Row    = Int
type Column = Int
type Value  = Int
type Grid   = [[Value]]

positions, values :: [Int]
positions = [1..9]
values    = [1..9]

blocks :: [[Int]]
blocks = [[1..3],[4..6],[7..9]]
\end{code}

Note that we let 0 represent a blank slot:

\begin{code}
showVal :: Value -> String
showVal 0 = " "
showVal d = show d
\end{code}
\begin{code}
showRow :: [Value] -> IO()
showRow [a1,a2,a3,a4,a5,a6,a7,a8,a9] = putStrLn . concat $
   [ "| ", showVal a1, " ", showVal a2, " ", showVal a3, " "
   , "| ", showVal a4, " ", showVal a5, " ", showVal a6, " "
   , "| ", showVal a7, " ", showVal a8, " ", showVal a9, " |" ]
showRow _ = error "invalid row"
\end{code}
\begin{code}
showGrid :: Grid -> IO ()
showGrid [as,bs,cs,ds,es,fs,gs,hs,is] =
 do putStrLn "+-------+-------+-------+"
    showRow as; showRow bs; showRow cs
    putStrLn "+-------+-------+-------+"
    showRow ds; showRow es; showRow fs
    putStrLn "+-------+-------+-------+"
    showRow gs; showRow hs; showRow is
    putStrLn "+-------+-------+-------+"
showGrid _ = error "invalid grid"
\end{code}
\begin{code}
type Sudoku = (Row,Column) -> Value
\end{code}
\begin{code}
sud2grid :: Sudoku -> Grid
sud2grid s =
  [ [ s (r,c) | c <- [1..9] ] | r <- [1..9] ]

grid2sud :: Grid -> Sudoku
grid2sud gr = \ (r,c) -> pos gr (r,c)
  where
  pos :: [[a]] -> (Row,Column) -> a
  pos gri (r,c) = (gri !! (r-1)) !! (c-1)
\end{code}
\begin{code}
showSudoku :: Sudoku -> IO ()
showSudoku = showGrid . sud2grid
\end{code}
\begin{code}
bl :: Int -> [Int]
bl x = concat $ filter (elem x) blocks
\end{code}

\subsection*{Sudoku with additional grids}
For the Sudoku with the four extra $3 \times 3$ blocks, we define additional blocks:

\begin{code}
addblocks :: [[Int]]
addblocks = [[2..4],[6..8]]
\end{code}
\begin{code}
addbl :: Int -> [Int]
addbl x = concat $ filter (elem x) addblocks
\end{code}

\subsection*{Restrictions}
We now define restrictions that distinguish between different parts of the
Sudoku that require injectivity. `Restriction' gives all coordinates of elements
of a certain restriction.

\begin{code}
type Restriction = (Row,Column) -> [(Row,Column)]
\end{code}
allValues gives you list of all values in a certain restriction.

\begin{code}
allValues :: Restriction -> Sudoku -> (Row, Column) -> [Value]
allValues res s (r,c) = map s (res (r,c))
\end{code}
\begin{code}
row :: Restriction
row (r,_) = [(r, c') | c' <- positions]
\end{code}
\begin{code}
column :: Restriction
column (_, c) = [ (r', c) | r' <- positions]
\end{code}
\begin{code}
subGrid :: Restriction
subGrid (r, c) = [ (r', c') | r' <- bl r, c' <- bl c]
\end{code}
\begin{code}
diagonalUp :: Restriction
diagonalUp (r, c) = [ (r',c') | r' <- positions, c' <- positions, (r' + c') == 10, (r + c) == 10 ]
\end{code}
\begin{code}
diagonalDown :: Restriction
diagonalDown (r,c) = [ (r',c') | r' <- positions, c' <- positions, r' == c', r == c]
\end{code}
\begin{code}
addsubGrid :: Restriction
addsubGrid (r,c) = [ (r', c') | r' <- addbl r, c' <- addbl c ]
\end{code}
\begin{code}
allRestrictions :: [Restriction]
allRestrictions = [row, column, subGrid, diagonalUp, diagonalDown, addsubGrid]
\end{code}
Free values are available values at open slot positions. First we define the
general free value function:

\begin{code}
freeInSeq :: [Value] -> [Value]
freeInSeq sequ = values \\ sequ
\end{code}
Then we apply freeInSeq to all the different restrictions that we defined before,
and intersect the result. This provides all the free values at a certain position
in the Sudoku.

\begin{code}
freeAtPos :: [Restriction] -> Sudoku -> (Row,Column) -> [Value]
freeAtPos x s (r,c) = foldr1 intersect [ freeInSeq (allValues res s (r,c)) | res <- x ]
\end{code}
The injectiveFor function now also takes into account the type of Sudoku.

\begin{code}
injective :: Eq a => [a] -> Bool
injective xs = nub xs == xs
\end{code}
\begin{code}
injectiveFor :: Restriction -> Sudoku -> (Row, Column) -> Bool
injectiveFor x s (r,c) = injective vs where
   vs = filter (/= 0) (map s $ x (r, c)) -- TODO think about this!
\end{code}
The consistent function checks for injectivity for every restriction:

\begin{code}
consistent :: [Restriction] -> Sudoku -> Bool
consistent x s =
   and [ injectiveFor res s (r,c) | res <- x, r <- positions, c <- positions]
\end{code}

\subsection*{Solving the Sudoku}
The code below implements the checks defined above by adding valid values to the
Sudoku problem.

\begin{code}
extend :: Sudoku -> ((Row,Column),Value) -> Sudoku
extend = update
\end{code}
\begin{code}
update :: Eq a => (a -> b) -> (a,b) -> a -> b
update f (y,z) x = if x == y then z else f x
\end{code}
\begin{code}
type Constraint = (Row,Column,[Value])
\end{code}
\begin{code}
type Node = (Sudoku,[Constraint])

showNode :: Node -> IO ()
showNode = showSudoku . fst
\end{code}
\begin{code}
solved  :: Node -> Bool
solved = null . snd
\end{code}
\begin{code}
extendNode :: [Restriction] -> Node -> Constraint -> [Node]
extendNode us (s,constr) (r,c,vs) =
   [(extend s ((r,c),v),
     sortBy length3rd $
         prune us (r,c,v) constr) | v <- vs ]
\end{code}
\begin{code}
length3rd :: (a,b,[c]) -> (a,b,[c]) -> Ordering
length3rd (_,_,zs) (_,_,zs') = compare (length zs) (length zs')
\end{code}
\begin{code}
prune :: [Restriction] -> (Row,Column,Value)
      -> [Constraint] -> [Constraint]
prune _  _ [] = []
prune us (r,c,v) ((x,y,zs):rest)
  | r == x = (x,y,zs\\[v]) : prune us (r,c,v) rest
  | c == y = (x,y,zs\\[v]) : prune us (r,c,v) rest
  | same us (r,c) (x,y) =
        (x,y,zs\\[v]) : prune us (r,c,v) rest
  | otherwise = (x,y,zs) : prune us (r,c,v) rest
\end{code}
The sameblock function has been replaced by `same`, which applies the general
sameFor function to every type of restriction that it needs. It returns True
whenever two positions are in the same (additional) subgrid or diagonal. The
condition that it is nonempty is needed so that it will not return True when
two elements are e.g. both not in any diagonal.

\begin{code}
sameFor :: Restriction -> (Row,Column) -> (Row,Column) -> Bool
sameFor u (r,c) (x,y) = (u (r,c) == u (x,y)) && not ( null (u (r, c)))
\end{code}
\begin{code}
same :: [Restriction] -> (Row,Column) -> (Row,Column) -> Bool
same us (r,c) (x,y) = or [ sameFor u (r,c) (x,y) | u <- us ]
\end{code}
\begin{code}
initNode :: Grid -> [Restriction] -> [Node]
initNode gr x = let s = grid2sud gr in
              if not (consistent x s) then []
              else [(s, constraints s x)]
\end{code}
\begin{code}
openPositions :: Sudoku -> [(Row,Column)]
openPositions s = [ (r,c) | r <- positions,
                            c <- positions,
                            s (r,c) == 0 ]
\end{code}
\begin{code}
constraints :: Sudoku -> [Restriction] -> [Constraint]
constraints s x = sortBy length3rd
    [(r,c, freeAtPos x s (r,c)) |
                       (r,c) <- openPositions s ]
\end{code}
The search function has been updated with a counter for the number of times that
a successor node is tried out. The solveAndShow and genAndSolve function output
this number.

\begin{code}
search :: Int -> (node -> [node])
       -> (node -> Bool) -> [node] -> ([node], Int)
search w _ _ [] = ([],w)
search w children goal (x:xs)
  | goal x    = (x : fst (search w children goal xs), w)
  | otherwise = search (w+1) children goal (children x ++ xs)
\end{code}
\begin{code}
solveNs :: [Restriction] -> [Node] -> ([Node], Int)
solveNs us = search 0 (succNode us) solved

succNode :: [Restriction] -> Node -> [Node]
succNode _ ( _ , [] ) = []
succNode us (s,p:ps) = extendNode us (s,ps) p
\end{code}
solveAndShow naturally now also takes into account the type of Sudoku.

\begin{code}
solveAndShow :: Grid -> [Restriction] -> IO ()
solveAndShow gr x = solveShowNs x (initNode gr x)
\end{code}
\begin{code}
solveShowNs :: [Restriction] -> [Node] -> IO ()
solveShowNs us = (\(ns,w) -> traverse showNode ns >> print [w]) . solveNs us
\end{code}
We define the following lists of restrictions to facilitate calling the solve function:
\begin{code}
normal :: [Restriction]
normal = [row, column, subGrid]
\end{code}
\begin{code}
diagonal :: [Restriction]
diagonal = [row, column, subGrid, diagonalUp, diagonalDown]
\end{code}
\begin{code}
addGrid :: [Restriction]
addGrid = [row, column, subGrid, addsubGrid]
\end{code}
Some predefined Sudoku examples that work with the right restriction set:

\subsection*{Example Sudokus}
\begin{code}
examplenormal :: Grid
examplenormal = [[5,3,0,0,7,0,0,0,0],
                 [6,0,0,1,9,5,0,0,0],
                 [0,9,8,0,0,0,0,6,0],
                 [8,0,0,0,6,0,0,0,3],
                 [4,0,0,8,0,3,0,0,1],
                 [7,0,0,0,2,0,0,0,6],
                 [0,6,0,0,0,0,2,8,0],
                 [0,0,0,4,1,9,0,0,5],
                 [0,0,0,0,8,0,0,7,9]]
\end{code}
\begin{code}
examplediag :: Grid
examplediag = [[0,0,0,0,0,0,0,4,0],
               [4,0,0,9,8,0,0,0,6],
               [0,3,0,0,0,7,9,8,0],
               [0,0,0,0,0,0,0,0,0],
               [0,0,5,7,0,4,1,0,0],
               [0,0,0,0,0,0,0,0,0],
               [0,6,3,8,0,0,0,5,0],
               [8,0,0,0,2,6,0,0,3],
               [0,1,0,0,0,0,0,0,0]]
\end{code}
\begin{code}
exampleadd :: Grid
exampleadd = [[0,0,2,0,0,0,0,0,0],
             [0,0,4,0,8,0,9,0,0],
             [0,0,0,3,0,0,0,0,0],
             [0,0,0,0,0,5,4,0,1],
             [0,0,0,0,0,0,0,0,0],
             [5,0,0,2,0,0,0,0,8],
             [0,0,0,0,0,6,0,7,0],
             [0,5,0,0,0,0,0,0,0],
             [0,0,0,0,3,0,0,1,0]]
\end{code}

\subsection*{Random Sudoku generation}
Now we provide code that generates random Sudokus of each type. A list of
restrictions is added as input argument to many functions to let it take into
account the Sudoku type.

\begin{code}
emptyN :: [Restriction] -> Node
emptyN x = (const 0, constraints (const 0) x)
\end{code}
\begin{code}
getRandomInt :: Int -> IO Int
getRandomInt n = getStdRandom (randomR (0,n))
\end{code}
\begin{code}
getRandomItem :: [a] -> IO [a]
getRandomItem [] = return []
getRandomItem xs = do n <- getRandomInt maxi
                      return [xs !! n]
                   where maxi = length xs - 1
\end{code}
\begin{code}
randomize :: Eq a => [a] -> IO [a]
randomize xs = do y <- getRandomItem xs
                  if null y
                    then return []
                    else do ys <- randomize (xs\\y)
                            return (head y:ys)
\end{code}
\begin{code}
sameLen :: Constraint -> Constraint -> Bool
sameLen (_,_,xs) (_,_,ys) = length xs == length ys
\end{code}
\begin{code}
getRandomCnstr :: [Constraint] -> IO [Constraint]
getRandomCnstr cs = getRandomItem (f cs)
  where f [] = []
        f (x:xs) = takeWhile (sameLen x) (x:xs)
\end{code}
\begin{code}
rsuccNode :: [Restriction] -> Node -> IO [Node]
rsuccNode y (s,cs) = do xs <- getRandomCnstr cs
                        if null xs
                          then return []
                          else return
                            (extendNode y (s,cs\\xs) (head xs))
\end{code}
\begin{code}
rsolveNs :: [Restriction] -> [Node] -> IO [Node]
rsolveNs y ns = rsearch (rsuccNode y) solved (return ns)
\end{code}
\begin{code}
rsearch :: (node -> IO [node])
            -> (node -> Bool) -> IO [node] -> IO [node]
rsearch succe goal ionodes =
  do xs <- ionodes
     if null xs
       then return []
       else
         if goal (head xs)
           then return [head xs]
           else do ys <- rsearch succe goal (succe (head xs))
                   if (not . null) ys
                      then return [head ys]
                      else if null (tail xs) then return []
                           else
                             rsearch
                               succe goal (return $ tail xs)
\end{code}
\begin{code}
genRandomSudoku :: [Restriction] -> IO Node
genRandomSudoku y = do [r] <- rsolveNs y [emptyN y]
                       return r
\end{code}
\begin{code}
uniqueSol :: [Restriction] -> Node -> Bool
uniqueSol w node = singleton (solveNs w [node]) where
  singleton ([],_) = False
  singleton ([_],_) = True
  singleton (_:_:_,_) = False
\end{code}
\begin{code}
eraseS :: Sudoku -> (Row,Column) -> Sudoku
eraseS s (r,c) (x,y) | (r,c) == (x,y) = 0
                     | otherwise      = s (x,y)
\end{code}
\begin{code}
eraseN :: [Restriction] -> Node -> (Row,Column) -> Node
eraseN x n (r,c) = (s, constraints s x)
  where s = eraseS (fst n) (r,c)
\end{code}
\begin{code}
minimalize :: [Restriction] -> Node -> [(Row,Column)] -> Node
minimalize _ n [] = n
minimalize x n ((r,c):rcs) | uniqueSol x n' = minimalize x n' rcs
                           | otherwise    = minimalize x n  rcs
  where n' = eraseN x n (r,c)
\end{code}
\begin{code}
filledPositions :: Sudoku -> [(Row,Column)]
filledPositions s = [ (r,c) | r <- positions,
                              c <- positions, s (r,c) /= 0 ]
\end{code}
\begin{code}
genProblem :: [Restriction] -> Node -> IO Node
genProblem x n = minimalize x n <$> randomize xs
     where xs = filledPositions (fst n)
\end{code}
sudGen generates a filled-in Sudoku of the right type (r), prints it, and
subsequently prints the problem version (s).

\begin{code}
sudGen :: [Restriction] -> IO (Sudoku,Sudoku)
sudGen x = do [r] <- rsolveNs x [emptyN x]
              s  <- genProblem x r
              return (fst r, fst s)
\end{code}

\subsection*{Generating and solving a Sudoku problem}
genAndSolve shows a random problem Sudoku of the right type, and continues to
solve it.
\begin{code}
genAndSolve :: [Restriction] -> IO ()
genAndSolve x = do (_,s) <- sudGen x
                   showSudoku s
                   solveAndShow (sud2grid s) x
\end{code}
To run the genAndSolve function multiple times the function below can be used,
or alternatively the replicateM function does the same thing.

\begin{code}
times :: Int -> [Restriction] -> IO ()
times 0 _ = return ()
times n x = do genAndSolve x
               times (n-1) x
\end{code}

-- | KFPT is an extension of the Lambda calculus to a simple functional core programming language
-- | KFPT introduces data types which, in contrast to the Church encoding for Lambda calculus,
-- | are represented through additional language constructs and are thus far easier to work with
-- | than representing data with functions.
module KFPT where

-- \| Imports
import Data.List (delete, deleteBy, find, nub, sort)
import Data.Maybe (fromMaybe)
import Debug.Trace (trace)

-- -------------------------------------------------------------

-- | Data Types

-- | Representation of KFPT expressions:
-- | The LambdaExpr type extends the basic lambda calculus with:
-- | - Cons: constructor applications to build data types
-- | - CaseT: case expressions to destruct data types
data LambdaExpr var
  = -- | Variable (represented as String)
    Var var
  | -- | Abstraction λx.s
    Lambda var (LambdaExpr var)
  | -- | Application (s t)
    App (LambdaExpr var) (LambdaExpr var)
  | -- | Constructor application c i args
    Cons Int [LambdaExpr var]
  | -- | Case expression case type s of {alts}
    CaseT String (LambdaExpr var) [Alt var]
  deriving (Eq, Show)

-- | Alternative pattern in a case expression (ci x1 ... xn -> e)
data Alt var = Alt Int [var] (LambdaExpr var)
  deriving (Eq, Show)

-- | Type synonym for LambdaExpr String to simplify usage
type LExp = LambdaExpr String

-- -------------------------------------------------------------

-- | Constructor Shortcuts

-- | Boolean constructors
true = Cons 1 []

false = Cons 2 []

-- | Pair constructor
pair = Cons 3

-- | List constructors
nil = Cons 4 []

cons = Cons 5

-- -------------------------------------------------------------

-- | Alternative Constructor Shortcuts

-- | Boolean alternatives
altTrue = Alt 1

altFalse = Alt 2

-- | Pair alternative
altPair = Alt 3

-- | List alternatives
altNil = Alt 4

altCons = Alt 5

-- -------------------------------------------------------------

-- | Type Information

-- | Arity of constructors (number of arguments)
arity :: Int -> Int
arity 1 = 0 -- true
arity 2 = 0 -- false
arity 3 = 2 -- pair
arity 4 = 0 -- nil
arity 5 = 2 -- cons

-- | Type of a constructor
typeOf :: Int -> String
typeOf 1 = "Bool"
typeOf 2 = "Bool"
typeOf 3 = "Pair"
typeOf 4 = "List"
typeOf 5 = "List"

-- | Constructors belonging to a type
constructors :: String -> [Int]
constructors "Bool" = [1, 2]
constructors "Pair" = [3]
constructors "List" = [4, 5]

-- -------------------------------------------------------------

-- | Wellformedness Checking

-- | Check if a LambdaExpr is well-formed - i.e., a valid KFPT expression
-- | This verifies that:
-- | - Constructor applications have the correct arity
-- | - Case alternatives are complete and disjoint
-- | - Pattern variables in alternatives are distinct
isWellformed :: (Eq var) => LambdaExpr var -> Bool
isWellformed (Var _) = True
isWellformed (Lambda x s) = isWellformed s
isWellformed (App s t) = isWellformed s && isWellformed t
isWellformed (Cons i args) =
  -- check if number of arguments is correct
  let n = arity i
   in length args == n && all isWellformed args
isWellformed (CaseT t s alts) =
  let checkAlts [] _ = False
      -- at last alt check if alts are complete and disjoint
      checkAlts [Alt i vars e] c =
        let n = length vars
            c' = c ++ [i]
         in -- check if alts have correct constructor and have wellformed e
            (n == arity i)
              && (n == length (nub vars))
              && isWellformed e
              -- at last alt check if alts are complete and disjoint
              && sort c' == constructors t
      checkAlts ((Alt i vars e) : as) c =
        let n = length vars
            c' = c ++ [i]
         in -- check if number of arguments is correct and pattern variables are distinct
            (n == arity i)
              && (n == length (nub vars))
              && isWellformed e
              && checkAlts as c'
   in isWellformed s && checkAlts alts []

-- -------------------------------------------------------------

-- | Examples for Wellformedness
example1 = CaseT "List" (cons [true, cons [false, nil]]) [altNil [] false, altCons ["x", "xs"] true]

example2 = CaseT "Bool" (cons [true, cons [false, nil]]) [altNil [] false, altCons ["x", "xs"] true]

example3 = CaseT "List" (cons [true, cons [false, nil]]) [altNil [] false, altCons ["x", "x"] true]

example4 = CaseT "List" (cons [true, cons [false, nil]]) [altNil [] false]

example5 = CaseT "List" (cons [true, cons [false, nil]]) [altNil [] false, altCons ["xs"] true]

example6 = cons [true]

example7 = Cons 1 [true]

example8 = true

example9 = cons [true, cons [false, nil]]

example10 = cons [Var "y", Var "z"]

example11 = cons [exampleIdId 3, exampleIdId 4]

-- | Test function for wellformedness examples
testWellFormed :: IO ()
testWellFormed =
  do
    putStrLn $ "Test 1: " ++ show (isWellformed (example1 :: LExp)) -- True
    putStrLn $ "Test 2: " ++ show (isWellformed (example2 :: LExp)) -- False
    putStrLn $ "Test 3: " ++ show (isWellformed (example3 :: LExp)) -- False
    putStrLn $ "Test 4: " ++ show (isWellformed (example4 :: LExp)) -- False
    putStrLn $ "Test 5: " ++ show (isWellformed (example5 :: LExp)) -- False
    putStrLn $ "Test 6: " ++ show (isWellformed (example6 :: LExp)) -- False
    putStrLn $ "Test 7: " ++ show (isWellformed (example7 :: LExp)) -- False
    putStrLn $ "Test 8: " ++ show (isWellformed (example8 :: LExp)) -- True
    putStrLn $ "Test 9: " ++ show (isWellformed (example9 :: LExp)) -- True
    putStrLn $ "Test 10: " ++ show (isWellformed (example10 :: LExp)) -- True
    putStrLn $ "Test 11: " ++ show (isWellformed (example11 :: LExp)) -- True

-- -------------------------------------------------------------

-- | Alpha Equivalence and Normal Forms

-- | Check if two expressions are alpha-equivalent
alphaEquiv s1 s2 =
  let (s1', _) = freshAlphaRename s1 names
      (s2', _) = freshAlphaRename s2 names
   in s1' == s2'

-- | Checks if a LambdaExpr is in functional weak head normal form (FWHNF)
isFWHNF :: LambdaExpr var -> Bool
isFWHNF (Lambda _ _) = True
isFWHNF _ = False

-- | Checks if a LambdaExpr is in constructor weak head normal form (CWHNF)
isCWHNF :: LambdaExpr var -> Bool
isCWHNF (Cons _ _) = True
isCWHNF _ = False

-- | Checks if a LambdaExpr is in weak head normal form (WHNF)
-- | An expression is in WHNF if it is either in FWHNF or CWHNF
isWHNF :: LambdaExpr var -> Bool
isWHNF e = isFWHNF e || isCWHNF e

-- | Test function for WHNF examples
testWHNF :: IO ()
testWHNF = do
  print (isWHNF example1) -- False
  print (isWHNF example8) -- True
  print (isWHNF example9) -- True
  print (isWHNF example10) -- True
  print (isWHNF example11) -- True
  print (isWHNF exampleI) -- True
  print (isFWHNF example1) -- False
  print (isFWHNF example8) -- False
  print (isFWHNF example9) -- False
  print (isFWHNF example10) -- False
  print (isFWHNF example11) -- False
  print (isFWHNF exampleI) -- True
  print (isCWHNF example1) -- False
  print (isCWHNF example8) -- True
  print (isCWHNF example9) -- True
  print (isCWHNF example10) -- True
  print (isCWHNF example11) -- True
  print (isCWHNF exampleI) -- False

-- -------------------------------------------------------------

-- | Call-by-Name Evaluation

-- | Try to perform a call-by-name reduction step
-- | Returns:
-- |  * Just (s',fresh') - if a reduction is possible, with the new expression and remaining fresh names
-- |  * Nothing - if no reduction is possible
tryCallByNameStep :: (Eq var) => LambdaExpr var -> [var] -> Maybe (LambdaExpr var, [var])
tryCallByNameStep (App (Lambda x s) t) fresh = Just $ substitute x t s fresh
tryCallByNameStep (App s t) fresh = case tryCallByNameStep s fresh of
  Nothing -> Nothing
  Just (s', fresh') -> Just (App s' t, fresh')
-- case reduction
tryCallByNameStep (CaseT typ (Cons i args) alts) fresh =
  -- get alt for constructor i
  let alt = find (\(Alt i' _ _) -> i == i') alts
   in case alt of
        Nothing -> Nothing -- case is directly dynamically untyped
        Just (Alt _ vars rhs) -> Just $ substituteParallel (zip vars args) rhs fresh
-- step into case expression
tryCallByNameStep (CaseT typ s alts) fresh = case tryCallByNameStep s fresh of
  Nothing -> Nothing
  Just (s', fresh') -> Just (CaseT typ s' alts, fresh')
tryCallByNameStep _ _ = Nothing

-- | Evaluate an expression using call-by-name strategy
-- | Returns only the final result of the evaluation
evaluateInCallByName :: LExp -> LExp
evaluateInCallByName s =
  let (s', fresh) = freshAlphaRename s names
   in evaluateCallByName s' fresh

-- | Helper for call-by-name evaluation with fresh name handling
evaluateCallByName :: (Eq var) => LambdaExpr var -> [var] -> LambdaExpr var
evaluateCallByName s fresh =
  case tryCallByNameStep s fresh of
    Just (s', fresh') -> evaluateCallByName s' fresh'
    Nothing -> s

-- | Trace the evaluation in Call-by-Name
-- | Returns a list of all intermediate expressions during evaluation
-- | The first element is the original expression, the last element is the result
traceEvaluateInCallByName :: LExp -> [LExp]
traceEvaluateInCallByName s =
  let (s', fresh) = freshAlphaRename s names
   in traceEvaluateCallByName s' fresh

-- | Helper for tracing call-by-name evaluation with fresh name handling
traceEvaluateCallByName :: (Eq var) => LambdaExpr var -> [var] -> [LambdaExpr var]
traceEvaluateCallByName s fresh =
  case tryCallByNameStep s fresh of
    Just (s', fresh') -> s : traceEvaluateCallByName s' fresh'
    Nothing -> [s]

-- | Helper function to print the evaluation steps
printTraceEvaluateCallByName :: LExp -> IO ()
printTraceEvaluateCallByName e =
  let xs = traceEvaluateInCallByName e
      expressions = map prettyMath xs
   in putStrLn $ unlines $ ("        " ++ head expressions) : map ("-name-> " ++) (tail expressions)

-- | Helper function to print a limited number of evaluation steps
printTraceEvaluateCallByNameLimit :: LExp -> Int -> IO ()
printTraceEvaluateCallByNameLimit e l =
  let xs = take l $ traceEvaluateInCallByName e
      expressions = map prettyMath xs
   in putStrLn $ unlines $ ("        " ++ head expressions) : map ("-name-> " ++) (tail expressions)

-- | Check if an expression converges in Call-by-Name
-- | An expression converges if it evaluates to WHNF
converges :: LExp -> Bool
converges e = isWHNF (evaluateInCallByName e)

-- | Test function for call-by-name examples
testCallByName :: IO ()
testCallByName = do
  printTraceEvaluateCallByName example12
  printTraceEvaluateCallByName example13

-- -------------------------------------------------------------

-- | Examples for Call-By-Name
example12 = CaseT "List" example11 [altNil [] false, altCons ["x", "xs"] (Var "x")]

example13 = CaseT "List" (cons [cons [true, nil], nil]) [altNil [] false, altCons ["x", "xs"] (Var "x")]

-- -------------------------------------------------------------

-- | Standard Lambda Calculus Examples

-- | I = λx.x (Identity function)
exampleI = Lambda "x" (Var "x")

-- | Omega = λx.(x x) (λx.(x x)) (Self-application, non-terminating)
exampleOmega =
  let o = Lambda "x" (App (Var "x") (Var "x"))
   in App o o

-- | K = λx.λy.x (First projection)
exampleK = Lambda "x" (Lambda "y" (Var "x"))

-- | K2 = λx.λy.y (Second projection)
exampleK2 = Lambda "x" (Lambda "y" (Var "y"))

-- | S = λx.λy.λz.(x z) (y z) (Substitution combinator)
exampleS = Lambda "x" (Lambda "y" (Lambda "z" (App (App (Var "x") (Var "z")) (App (Var "y") (Var "z")))))

-- | Y = λf.(λx.(f (x x))) (λx.(f (x x))) (Y combinator - fixed point)
exampleY =
  let y = Lambda "x" (App (Var "f") (App (Var "x") (Var "x")))
   in Lambda "f" (App y y)

-- | Z= λf.(λx.(f λz.(x x) z)) (λx.(f λz.(x x) z)) (Z combinator - call-by-value Y)
exampleZ =
  let lamz = Lambda "z" (App (App (Var "x") (Var "x")) (Var "z"))
      z = Lambda "x" (App (Var "f") lamz)
   in Lambda "f" (App z z)

-- | (Y K) (Y combinator applied to K)
exampleTop = App exampleY exampleK

-- | (Y K) I ... I (Multiple I applications)
exampleTopId 0 = exampleTop
exampleTopId i = App (exampleTopId (i - 1)) exampleI

-- | (I I) ... (I I) (Multiple self-applications of I)
exampleIdId 0 = App exampleI exampleI
exampleIdId i = App (exampleIdId (i - 1)) (App exampleI exampleI)

-- | An open expression with free variables
-- | ((λx.(g (λz.((x y) z)))) (λu.(g (λz.((u y) u)))))
exampleOpen1 =
  App
    ( Lambda
        "x"
        (App (Var "g") (Lambda "z" (App (App (Var "x") (Var "y")) (Var "z"))))
    )
    ( Lambda
        "u"
        (App (Var "g") (Lambda "z" (App (App (Var "u") (Var "y")) (Var "u"))))
    )

-- -------------------------------------------------------------

-- | Pretty Printers

-- | Print expressions in mathematical notation
prettyMath :: LExp -> String
prettyMath (Lambda x s) = "(λ" ++ x ++ "." ++ prettyMath s ++ ")"
prettyMath (Var x) = x
prettyMath (App s t) = "(" ++ prettyMath s ++ " " ++ prettyMath t ++ ")"
prettyMath (Cons i args) = "(c" ++ show i ++ " " ++ unwords (map prettyMath args) ++ ")"
prettyMath (CaseT typ s alts) = "case_" ++ typ ++ " " ++ prettyMath s ++ " of {" ++ unwords (map prettyAlt alts) ++ "}"
  where
    prettyAlt (Alt i vars rhs) = "(c" ++ show i ++ " " ++ unwords vars ++ ")" ++ " -> " ++ prettyMath rhs ++ ";"

-- | Format and print in mathematical notation
printPrettyMath :: LExp -> IO ()
printPrettyMath = putStrLn . prettyMath

-- -------------------------------------------------------------

-- | Free and Bound Variables

-- | Computes the set of free variables in a lambda expression
-- | In case expressions, variables are bound in the pattern
freeVars :: (Eq var) => LambdaExpr var -> [var]
freeVars e = nub (fv e)
  where
    fv (Var v) = [v]
    fv (Lambda x s) = delete x (fv s)
    fv (App s t) = fv s ++ fv t
    fv (Cons _ args) = concatMap fv args
    fv (CaseT _ s alts) = fv s ++ concatMap (\(Alt _ vars rhs) -> deleteAll vars (fv rhs)) alts

    deleteAll xs ys = foldl (flip delete) ys xs

-- | Computes the set of bound variables in a lambda expression
boundVars :: (Eq var) => LambdaExpr var -> [var]
boundVars e = nub (bv e)
  where
    bv (Var v) = []
    bv (Lambda x s) = x : bv s
    bv (App s t) = bv s ++ bv t
    bv (Cons _ args) = concatMap bv args
    bv (CaseT _ s alts) = bv s ++ concatMap (\(Alt _ vars rhs) -> vars ++ bv rhs) alts

-- -------------------------------------------------------------

-- | Variable Convention

-- | Check distinct variable convention (DVC):
-- | - The intersection of free and bound variables should be empty
-- | - All bound variables should be unique
-- | Returns True if the convention is satisfied, False otherwise
checkDistinctVariableConvention :: (Eq var) => LambdaExpr var -> Bool
checkDistinctVariableConvention e =
  let bvars = boundVars e
      fvars = freeVars e
   in not $ any (`elem` fvars) bvars || any (`elem` bvars) fvars || length bvars /= length (nub bvars)

-- -------------------------------------------------------------

-- | Alpha Renaming

-- | Rename variables in a lambda expression using a list of fresh names
-- | Returns:
-- |  * A fresh alpha-renamed copy of the expression where all binders and
-- |    corresponding occurrences are consistently renamed
-- |  * The unused fresh names
-- | Note: Behavior is undefined if fresh names list is insufficient
freshAlphaRename :: (Eq var) => LambdaExpr var -> [var] -> (LambdaExpr var, [var])
freshAlphaRename e fresh = freshAlphaRenameIt e id fresh
  where
    freshAlphaRenameIt (Var v) mappings fresh = (Var (mappings v), fresh)
    freshAlphaRenameIt (App s t) mappings fresh =
      let (s', fresh') = freshAlphaRenameIt s mappings fresh
          (t', fresh'') = freshAlphaRenameIt t mappings fresh'
       in (App s' t', fresh'')
    freshAlphaRenameIt (Lambda x s) mappings (f : fresh) =
      let mappings' var = if var == x then f else mappings var
          (s', fresh') = freshAlphaRenameIt s mappings' fresh
       in (Lambda f s', fresh')
    freshAlphaRenameIt (Cons num args) mappings fresh =
      let (args', fresh') = go args mappings fresh
          go [] _ fresh = ([], fresh)
          go (a : as) mappings fresh =
            let (a', fresh') = freshAlphaRenameIt a mappings fresh
                (as', fresh'') = go as mappings fresh'
             in (a' : as', fresh'')
       in (Cons num args', fresh')
    freshAlphaRenameIt (CaseT typ s alts) mappings fresh =
      let go [] fresh = ([], fresh)
          go ((Alt i patvars rhs) : as) fresh =
            let (patvars', fresh') = splitAt (length patvars) fresh
                mappings' x = fromMaybe (mappings x) (lookup x (zip patvars patvars'))
                (rhs', fresh'') = freshAlphaRenameIt rhs mappings' fresh'
                (as', fresh''') = go as fresh''
             in (Alt i patvars' rhs' : as', fresh''')
          (s', fresh') = freshAlphaRenameIt s mappings fresh
          (alts', fresh'') = go alts fresh'
       in (CaseT typ s' alts', fresh'')

-- | Useful fresh names for renaming: ["x1", "x2", ...]
names = [read ("x" ++ show i) | i <- [1 ..]]

-- | Helper function to test alpha renaming
testfreshAlphaRename :: LExp -> LExp
testfreshAlphaRename e = fst (freshAlphaRename e names)

-- -------------------------------------------------------------

-- | Substitution

-- | Single substitution wrapper for parallel substitution
substitute :: (Eq var) => var -> LambdaExpr var -> LambdaExpr var -> [var] -> (LambdaExpr var, [var])
substitute x t = substituteParallel [(x, t)]

-- | Parallel substitution
-- | substituteParallel [(x1,s1),...,(xn,sn)] t fresh
-- | Applies the parallel substitution t[s1/x1,...,sn/xn] and
-- | renames each substituted si with freshAlphaRename
-- | Returns (t[s1/x1,...,sn/xn],fresh') where fresh' are the
-- | remaining unused fresh names
substituteParallel :: (Eq var) => [(var, LambdaExpr var)] -> LambdaExpr var -> [var] -> (LambdaExpr var, [var])
substituteParallel mapping (Var y) fresh
  -- lookup y and replace it or keep it
  | Just t <- lookup y mapping = freshAlphaRename t fresh
  | otherwise = (Var y, fresh)
substituteParallel mapping (Lambda y s) fresh =
  -- remove y from mapping to avoid capture and substitute in s
  let mapping' = deleteBy (\(a, _) (b, _) -> a == b) (y, undefined) mapping
      (s', fresh') = substituteParallel mapping' s fresh
   in (Lambda y s', fresh')
substituteParallel mapping (App r s) fresh =
  -- substitute in r and s
  let (r', fresh') = substituteParallel mapping r fresh
      (s', fresh'') = substituteParallel mapping s fresh'
   in (App r' s', fresh'')
substituteParallel mapping (Cons i args) fresh =
  -- substitute in args
  let (args', fresh') = substituteParallelList mapping args fresh
   in (Cons i args', fresh')
  where
    -- return empty list if no args are left
    substituteParallelList _ [] fresh = ([], fresh)
    -- substitute in first arg and continue with rest
    substituteParallelList mapping (x : xs) fresh =
      let (x', fresh') = substituteParallel mapping x fresh
          (xs', fresh'') = substituteParallelList mapping xs fresh'
       in (x' : xs', fresh'')
substituteParallel mapping (CaseT typ e alts) fresh =
  -- substitute in e and all alts
  let (e', fresh') = substituteParallel mapping e fresh
      (alts', fresh'') = substituteParallelAlts mapping alts fresh'
   in (CaseT typ e' alts', fresh'')
  where
    -- return empty list if no alts are left
    substituteParallelAlts _ [] fresh = ([], fresh)
    -- substitute in first alt and continue with rest
    substituteParallelAlts mapping (Alt i vars expr : rest) fresh =
      -- remove all variables bound in the pattern from the mapping
      let mapping' = foldr (\var m -> deleteBy (\(a, _) (b, _) -> a == b) (var, undefined) m) mapping vars
          (expr', fresh') = substituteParallel mapping' expr fresh
          (rest', fresh'') = substituteParallelAlts mapping rest fresh'
       in (Alt i vars expr' : rest', fresh'')

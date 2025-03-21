-- | Haskell implementation of the Lambda Calculus
module LambdaCalculus where

-- \| Imports
import Data.List (intersect, union, (\\))
import Data.Maybe (catMaybes)

-- -------------------------------------------------------------

-- | Data Types

-- | Represents a generic lambda expression
data LambdaExpr var
  = -- | Variable (represented as String)
    Var var
  | -- | Abstraction λx.s
    Lambda var (LambdaExpr var)
  | -- | Application (s t)
    App (LambdaExpr var) (LambdaExpr var)
  deriving (Eq, Show)

-- | Type synonym for LambdaExpr String to simplify usage
type LExp = LambdaExpr String

-- -------------------------------------------------------------

-- | Examples

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
  let z = Lambda "x" (App (Var "f") (Lambda "z" (App (App (Var "x") (Var "x")) (Var "z"))))
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

-- | Expression with double binding of same variable
exampleDoubleBind = Lambda "x" (Lambda "x" (Var "x"))

-- -------------------------------------------------------------

-- | Pretty Printers

-- | Print expressions in mathematical notation
prettyMath :: LExp -> String
prettyMath (Lambda x s) = "(λ" ++ x ++ "." ++ prettyMath s ++ ")"
prettyMath (Var x) = x
prettyMath (App s t) = "(" ++ prettyMath s ++ " " ++ prettyMath t ++ ")"

-- | Format and print in mathematical notation
printPrettyMath = putStrLn . prettyMath

-- | Print expressions in Haskell notation
prettyHaskell :: LExp -> String
prettyHaskell (Lambda x s) = "(\\" ++ x ++ " -> " ++ prettyHaskell s ++ ")"
prettyHaskell (Var x) = x
prettyHaskell (App s t) = "(" ++ prettyHaskell s ++ " " ++ prettyHaskell t ++ ")"

-- | Format and print in Haskell notation
printPrettyHaskell = putStrLn . prettyHaskell

-- | Helper function for forcing evaluation
evaluate x = seq x ()

-- -------------------------------------------------------------

-- | Free and Bound Variables

-- | Computes the set of free variables in a lambda expression
freeVars :: (Eq var) => LambdaExpr var -> [var]
freeVars (Var x) = [x]
freeVars (Lambda x s) = freeVars s \\ [x] -- Remove bound variable from free vars
freeVars (App s t) = freeVars s `union` freeVars t

-- | Computes the set of bound variables in a lambda expression
boundVars :: (Eq var) => LambdaExpr var -> [var]
boundVars (Var _) = []
boundVars (Lambda x s) = [x] `union` boundVars s
boundVars (App s t) = boundVars s `union` boundVars t

-- -------------------------------------------------------------

-- | Variable Convention

-- | Check distinct variable convention:
-- | - The intersection of free and bound variables should be empty
-- | - All variables in bindings should be pairwise different
-- | Returns True if the convention is satisfied, False otherwise
checkDistinctVariableConvention :: (Eq var) => LambdaExpr var -> Bool
checkDistinctVariableConvention e =
  let distinctVars (Var _) = True
      distinctVars (Lambda x s) = x `notElem` boundVars s && distinctVars s
      distinctVars (App s t) = distinctVars s && distinctVars t
      f = freeVars e
      b = boundVars e
   in null (f `intersect` b) && distinctVars e

-- -------------------------------------------------------------

-- | Alpha Renaming

-- | Rename variables in a lambda expression using a list of fresh names
-- | Returns:
-- |  * A fresh alpha-renamed copy of the expression (all binders and corresponding occurrences
-- |    are consistently renamed) using fresh names from the provided list
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

-- | Useful fresh names for renaming: ["x1", "x2", ...]
names = ["x" ++ show i | i <- [1 ..]]

-- | Helper function to test the alpha renaming
testfreshAlphaRename e = fst (freshAlphaRename e names)

-- -------------------------------------------------------------

-- | Beta Reduction

-- | Try to reduce a lambda expression using direct beta reduction
-- | Returns:
-- |  * Nothing if reduction is not possible
-- |  * Just (e, fresh') where e is the expression after beta reduction
-- |    and fresh' are the unused fresh names
-- | Note: Ensures distinct variable convention via alpha-renaming
directBetaReduction :: (Eq var) => LambdaExpr var -> [var] -> Maybe (LambdaExpr var, [var])
directBetaReduction (App (Lambda x s) t) fresh = Just (substitute x t s fresh)
directBetaReduction _ _ = Nothing

-- | Performs substitution s[t/x] with appropriate alpha-renaming
-- | For each substitution of x by t, expression t is renamed using fresh names
-- | Returns the pair (s[t/x], fresh') where fresh' are the unused fresh names
substitute :: (Eq var) => var -> LambdaExpr var -> LambdaExpr var -> [var] -> (LambdaExpr var, [var])
substitute x t (Var y) fresh
  | x == y = freshAlphaRename t fresh -- Substitute if variable matches
  | otherwise = (Var y, fresh) -- Otherwise keep the variable unchanged
substitute x t (Lambda y s) fresh
  | x == y = (Lambda y s, fresh) -- If bound variable matches, don't substitute
  | y `elem` freeVars t -- If bound variable occurs free in t, rename
    =
      let (Lambda y' s', fresh') = freshAlphaRename (Lambda y s) fresh
       in substitute x t (Lambda y' s') fresh'
  | otherwise -- Otherwise substitute in the body
    =
      let (s', fresh') = substitute x t s fresh
       in (Lambda y s', fresh')
substitute x t (App r s) fresh =
  -- Substitute in both subexpressions
  let (r', fresh') = substitute x t r fresh
      (s', fresh'') = substitute x t s fresh'
   in (App r' s', fresh'')

-- | Helper to run and display direct beta reduction
tryDirectBeta e =
  let (e', names') = freshAlphaRename e names
   in maybe (putStrLn "no direct β-reduction possible") (\(e'', _) -> putStrLn $ prettyMath e ++ " -β-> " ++ prettyMath e'') (directBetaReduction e' names')

-- -------------------------------------------------------------

-- | Deep Beta Reduction

-- | Test if an expression has a β-Redex at any position
hasDeepBetaRedex :: LambdaExpr var -> Bool
hasDeepBetaRedex (Var _) = False
hasDeepBetaRedex (App (Lambda _ _) _) = True
hasDeepBetaRedex (Lambda _ e) = hasDeepBetaRedex e
hasDeepBetaRedex (App e1 e2) = hasDeepBetaRedex e1 || hasDeepBetaRedex e2

-- | Computes all possible beta reductions s' for a given expression s
-- | where s -C,β-> s' using a list of fresh names
-- | Returns a list of pairs (s', fresh') where fresh' are the unused fresh names
deepBeta :: (Eq var) => LambdaExpr var -> [var] -> [(LambdaExpr var, [var])]
deepBeta (Var _) _ = []
deepBeta (Lambda x e) fresh =
  -- Reduce under lambda
  [(Lambda x e', fresh') | (e', fresh') <- deepBeta e fresh]
deepBeta (App (Lambda x s) t) fresh =
  -- Direct beta reduction possible
  let base = case directBetaReduction (App (Lambda x s) t) fresh of
        Just result -> [result]
        Nothing -> []
      -- Reduce under body s and argument t separately
      sReductions = [(App (Lambda x s') t, fresh') | (s', fresh') <- deepBeta s fresh]
      tReductions = [(App (Lambda x s) t', fresh') | (t', fresh') <- deepBeta t fresh]
   in base ++ sReductions ++ tReductions
deepBeta (App s t) fresh =
  -- Reduce under both subexpressions separately
  [(App s' t, fresh') | (s', fresh') <- deepBeta s fresh]
    ++ [(App s t', fresh') | (t', fresh') <- deepBeta t fresh]

-- | Helper to print the -C,β-> reductions
doDeepBeta e =
  let (e', names') = freshAlphaRename e names
   in putStrLn $ unlines $ map (\(e', _) -> prettyMath e ++ " -β-> " ++ prettyMath e') (deepBeta e' names')

-- -------------------------------------------------------------

-- | Parallel One Reduction

-- | Computes all parallel one reductions s' for a given expression s
-- | where s ->_1 s' using a list of fresh names
-- | Returns a list of pairs (s', fresh') where fresh' are the unused fresh names
-- |
-- | The parallel one reduction is defined as:
-- |  - s ->_1 s
-- |  - If s1 ->_1 s2 and t1 ->_1 t2, then (s1 s2) ->_1 (t1 t2)
-- |  - If s1 ->_1 s2 and t1 ->_1 t2, then ((λx.s1) t1) ->_1 s2[t2/x]
-- |  - If s ->_1 t, then λx.s -> λx.t
parallelOneReduction :: (Eq var) => LambdaExpr var -> [var] -> [(LambdaExpr var, [var])]
parallelOneReduction (Var x) fresh = [(Var x, fresh)] -- Variables reduce to themselves
parallelOneReduction (Lambda x e) fresh =
  -- Reduce under lambda
  [(Lambda x e', fresh') | (e', fresh') <- parallelOneReduction e fresh]
parallelOneReduction (App (Lambda x s) t) fresh =
  -- Direct beta reduction possible, but also reduce under body s and argument t
  let sReductions = parallelOneReduction s fresh
      tReductions = parallelOneReduction t fresh
      -- Now for each combination of reduced body and argument, perform beta reduction
      betaReductions =
        [ directBetaReduction (App (Lambda x s') t') fresh''
          | (s', fresh') <- sReductions,
            (t', fresh'') <- tReductions
        ]
      -- Also include expressions without beta step
      doNothingReductions =
        [ (App (Lambda x s') t', fresh'')
          | (s', fresh') <- sReductions,
            (t', fresh'') <- tReductions
        ]
   in catMaybes betaReductions ++ doNothingReductions
parallelOneReduction (App s t) fresh =
  -- Reduce subexpressions
  [ (App s' t', fresh'')
    | (s', fresh') <- parallelOneReduction s fresh,
      (t', fresh'') <- parallelOneReduction t fresh'
  ]

-- | Helper to print the ->_1 reductions
doParallelOneReduction e =
  let (e', names') = freshAlphaRename e names
   in putStrLn $ unlines $ map (\(e', _) -> prettyMath e ++ " ->_1 " ++ prettyMath e') (parallelOneReduction e' names')

-- -------------------------------------------------------------

-- | Main function to demonstrate examples
main = do
  putStrLn $ unlines $ map show [exampleI, exampleOmega, exampleK, exampleK2, exampleY, exampleZ, exampleTop, exampleTopId 5, exampleIdId 5, exampleOpen1]
  mapM_ printPrettyMath [exampleI, exampleOmega, exampleK, exampleK2, exampleY, exampleZ, exampleTop, exampleTopId 5, exampleIdId 5, exampleOpen1]
  mapM_ printPrettyHaskell [exampleI, exampleOmega, exampleK, exampleK2, exampleY, exampleZ, exampleTop, exampleTopId 5, exampleIdId 5, exampleOpen1]
  mapM_ (print . freeVars) [exampleI, exampleOmega, exampleK, exampleK2, exampleY, exampleZ, exampleTop, exampleTopId 5, exampleIdId 5, exampleOpen1]
  mapM_ (print . boundVars) [exampleI, exampleOmega, exampleK, exampleK2, exampleY, exampleZ, exampleTop, exampleTopId 5, exampleIdId 5, exampleOpen1]
  mapM_ (print . checkDistinctVariableConvention) [exampleI, exampleOmega, exampleK, exampleK2, exampleY, exampleZ, exampleTop, exampleTopId 5, exampleIdId 5, exampleOpen1]
  mapM_ (print . testfreshAlphaRename) [exampleI, exampleOmega, exampleK, exampleK2, exampleY, exampleZ, exampleTop, exampleTopId 5, exampleIdId 5, exampleOpen1]
  mapM_ tryDirectBeta [exampleI, exampleOmega, exampleK, exampleK2, exampleY, exampleZ, exampleTop, exampleTopId 5, exampleIdId 5, exampleOpen1]
  mapM_ doDeepBeta [exampleI, exampleOmega, exampleK, exampleK2, exampleY, exampleZ, exampleTop, exampleTopId 5, exampleIdId 5, exampleOpen1]
  mapM_ doParallelOneReduction [exampleI, exampleOmega, exampleK, exampleK2, exampleY, exampleZ, exampleTop, exampleTopId 5, exampleIdId 5, exampleOpen1]

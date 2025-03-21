-- | Module for refuting contextual equivalence of lambda expressions
module RefuteConEq where

-- \| Imports
import Data.List

-- -------------------------------------------------------------

-- | Data Types

-- | Represents a lambda expression with additional constructs for refuting contextual equivalence
data LambdaExpr var
  = -- | Variable representation (e.g., Var "x")
    Var var
  | -- | Abstraction λx.s represented as Lambda "x" s
    Lambda var (LambdaExpr var)
  | -- | Application (s t) represented as App s t
    App (LambdaExpr var) (LambdaExpr var)
  | -- | Divergence symbol representing non-terminating expressions
    Bot
  | -- | Context hole symbol
    Hole
  deriving (Eq, Show) -- Automatically generate instances for Eq and Show typeclasses

-- | Type synonym for LambdaExpr with String variables
type LExp = LambdaExpr String

-- -------------------------------------------------------------

-- | Core Functionality

-- | The goal of this module is to automatically refute contextual equivalence
-- | of lambda expressions by finding, for given expressions s1 and s2,
-- | a context C such that C[s1] converges but C[s2] diverges, or vice versa:
-- | C[s1] diverges but C[s2] converges.
-- | Since convergence and divergence of lambda expressions is not decidable,
-- | we can only implement a correct but incomplete procedure.

-- | Convergence test: Instead of using the previous converges function,
-- | we now use convergesLimit, which checks if a lambda expression
-- | converges within a maximum of l steps.
convergesLimit :: Int -> LExp -> Bool
convergesLimit limit e = isFWHNF $ last $ take limit $ traceEvaluateInCallByName e

-- | Divergence test: Testing for divergence is also challenging as we would need
-- | to observe potentially infinite reductions. We use two approaches:
-- |
-- | 1. We added a Bot constant to our LambdaExpr datatype:
-- |    Bot represents a closed non-terminating expression that we can recognize.
-- |    We have confirmed divergence if an expression s evaluates in call-by-name
-- |    to an expression R[Bot], where Bot is in a reduction context.
-- |
-- | 2. We use a cycle detection function called hasLoop.

-- | Checks if an expression is of the form R[Bot]
isRBot :: LambdaExpr var -> Bool
isRBot Bot = True
isRBot (App s t) = isRBot s
isRBot _ = False

-- | Checks if the evaluation trace contains a loop
-- | The function receives a list of reduction successors
-- | (if s0 -name-> s1 -name-> s2 .... -name-> sn, then hasLoop gets
-- | [s0,s1,s2,...,sn] as input)
-- | It checks if there exists a loop si -> si+1 ->...-> sj where si =_α sj
-- | and at least one step was made (=_α is alpha-equivalence)
hasLoop :: [LExp] -> Bool
hasLoop [] = False
hasLoop (x : xs) = checkLoopFromHere x xs || hasLoop xs
  where
    -- Check if the current expression forms a loop with any later expression
    checkLoopFromHere :: LExp -> [LExp] -> Bool
    checkLoopFromHere _ [] = False
    checkLoopFromHere current (y : ys) =
      -- If current expression is alpha-equivalent to y, we found a loop
      alphaEquiv current y || checkLoopFromHere current ys

-- | Test alpha-equivalence of two expressions
alphaEquiv :: LExp -> LExp -> Bool
alphaEquiv s1 s2 =
  let (s1', _) = freshAlphaRename s1 names
      (s2', _) = freshAlphaRename s2 names
   in s1' == s2'

-- | divergesLimit generates the reduction successors and
-- | calls both divergence tests
divergesLimit :: Int -> LExp -> Bool
divergesLimit limit e =
  let evTrace = take limit $ traceEvaluateInCallByName e
   in isRBot (last evTrace) || hasLoop evTrace

-- -------------------------------------------------------------

-- | Context and Expression Generation

-- | The expressions function generates all possible lambda expressions
-- | with a maximum depth of i:
-- | - Var x and Bot have depth 0
-- | - (Lambda x s) has depth 1 + depth(s)
-- | - App s t has depth 1 + depth(s) + depth(t)
-- | For testing, we start with a small set of variable names (e.g., 3 different names)
sampleNames :: [String]
sampleNames = take 3 names

-- | Generate all expressions up to depth i
expressions 0 = Bot : [Var x | x <- sampleNames]
expressions i =
  -- Collect all expressions from the base case
  expressions 0
    ++
    -- Generate abstractions (λx.s) by combining each variable with each possible subexpression
    [Lambda x s | x <- sampleNames, s <- expressions (i - 1)]
    ++
    -- Generate applications (s t) by combining each pair of possible smaller expressions
    -- Split the depth between s and t using generator j in [0..i-1]
    -- Combine expressions s with depth j and t with depth i-1-j (remaining depth)
    [App s t | j <- [0 .. i - 1], s <- expressions j, t <- expressions (i - 1 - j)]

-- | contexts i generates reduction contexts
-- | (for closed expressions these should suffice (due to the context lemma),
-- | for open ones we could test even more, but we skip that),
-- | where R[] is represented as a Haskell function \x -> R[x],
-- | i.e., applying a context c to a LExp s gives a LExp (which then represents R[s])
-- | Here, the depth of the contexts is limited by the depth limit i.
-- | The empty context is exactly the identity function:
contexts 0 = [id]
contexts i =
  -- Include base case
  contexts 0
    ++
    -- Generate contexts of the form: ([] e) with e having a maximum depth of i - 1
    [(\hole -> App (c hole) e) | j <- [0 .. i - 1], e <- expressions j, c <- contexts (i - 1 - j)]

-- | refuteConEq performs the search for a counterexample
-- | The parameters i and l might need adjustment depending on
-- | how the contexts are generated
refuteConEq :: LExp -> LExp -> [String]
refuteConEq s1 s2 =
  [ "For context C = "
      ++ prettyMath (c Hole)
      ++ ", expression"
      ++ " C["
      ++ prettyMath s1
      ++ "]"
      ++ ( if convergesLimit l (c s1)
             then convergeSym
             else
               if divergesLimit l (c s1)
                 then divergeSym
                 else "?"
         )
      ++ " and expression"
      ++ " C["
      ++ prettyMath s2
      ++ "]"
      ++ ( if convergesLimit l (c s2)
             then convergeSym
             else
               if divergesLimit l (c s2)
                 then divergeSym
                 else "?"
         )
    | i <- [1, 2 ..],
      let l = 100 + i,
      c <- contexts i,
      (convergesLimit l (c s1) && divergesLimit l (c s2))
        || (divergesLimit l (c s1) && convergesLimit l (c s2))
  ]

-- | Symbols for convergence and divergence
convergeSym :: String
convergeSym = "⇓"

divergeSym :: String
divergeSym = "⇑"

-- | Print only the first counterexample
runRefute :: LExp -> LExp -> IO ()
runRefute s1 s2 = mapM_ putStrLn $ take 1 $ refuteConEq s1 s2

-- -------------------------------------------------------------

-- | Examples

-- | Example test cases
main :: IO ()
main =
  do
    runRefute Bot exampleI
    runRefute exampleK exampleK2
    runRefute churchZero churchOne
    runRefute churchOne churchTwo
    runRefute churchTwo churchThree

-- | Church numerals
churchZero :: LExp
churchZero = Lambda "f" (Lambda "x" (Var "x"))

churchOne :: LExp
churchOne = Lambda "f" (Lambda "x" (App (Var "f") (Var "x")))

churchTwo :: LExp
churchTwo = Lambda "f" (Lambda "x" (App (Var "f") (App (Var "f") (Var "x"))))

churchThree :: LExp
churchThree = Lambda "f" (Lambda "x" (App (Var "f") (App (Var "f") (App (Var "f") (Var "x")))))

-- -------------------------------------------------------------

-- | Helper Functions

-- | Check if a lambda expression is in functional weak head normal form (FWHNF)
isFWHNF :: LambdaExpr var -> Bool
isFWHNF (Lambda _ _) = True
isFWHNF _ = False

-- -------------------------------------------------------------

-- | Call-by-name Evaluation

-- | Try to perform a call-by-name reduction step
-- | Returns:
-- |  * Just (s,names) if a reduction is possible
-- |  * Nothing if no reduction is possible
tryCallByNameStep :: (Eq var) => LambdaExpr var -> [var] -> Maybe (LambdaExpr var, [var])
tryCallByNameStep (App (Lambda x s) t) fresh = Just $ substitute x t s fresh
tryCallByNameStep (App s t) fresh = case tryCallByNameStep s fresh of
  Nothing -> Nothing
  Just (s', fresh') -> Just (App s' t, fresh')
tryCallByNameStep _ _ = Nothing

-- | Evaluate an expression using call-by-name strategy until no more reductions are possible
-- | Uses fresh names for renaming and performs initial alpha-renaming before evaluation
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

-- | Trace the evaluation in call-by-name
-- | Returns a list of all expressions after each step,
-- | with the result at the end of the list.
-- | The list is generated lazily, so the first n elements can be
-- | accessed even if the list is infinite.
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

-- | Print all steps of call-by-name evaluation
printTraceEvaluateCallByName :: LExp -> IO ()
printTraceEvaluateCallByName e =
  let xs = traceEvaluateInCallByName e
      expressions = map prettyMath xs
   in putStrLn $ unlines $ ("        " ++ head expressions) : map ("-name-> " ++) (tail expressions)

-- | Print the first l steps of call-by-name evaluation
printTraceEvaluateCallByNameLimit :: LExp -> Int -> IO ()
printTraceEvaluateCallByNameLimit e l =
  let xs = take l $ traceEvaluateInCallByName e
      expressions = map prettyMath xs
   in putStrLn $ unlines $ ("        " ++ head expressions) : map ("-name-> " ++) (tail expressions)

-- | Check if an expression converges in call-by-name evaluation
converges :: LExp -> Bool
converges e = isFWHNF (evaluateInCallByName e)

-- -------------------------------------------------------------

-- | Standard Lambda Calculus Examples

-- | I = λx.x (Identity function)
exampleI :: LExp
exampleI = Lambda "x" (Var "x")

-- | Omega = λx.(x x) (λx.(x x)) (Self-application, non-terminating)
exampleOmega :: LExp
exampleOmega =
  let o = Lambda "x" (App (Var "x") (Var "x"))
   in App o o

-- | K = λx.λy.x (First projection)
exampleK :: LExp
exampleK = Lambda "x" (Lambda "y" (Var "x"))

-- | K2 = λx.λy.y (Second projection)
exampleK2 :: LExp
exampleK2 = Lambda "x" (Lambda "y" (Var "y"))

-- | S = λx.λy.λz.(x z) (y z) (Substitution combinator)
exampleS :: LExp
exampleS = Lambda "x" (Lambda "y" (Lambda "z" (App (App (Var "x") (Var "z")) (App (Var "y") (Var "z")))))

-- | Y = λf.(λx.(f (x x))) (λx.(f (x x))) (Y combinator - fixed point)
exampleY :: LExp
exampleY =
  let y = Lambda "x" (App (Var "f") (App (Var "x") (Var "x")))
   in Lambda "f" (App y y)

-- | Z= λf.(λx.(f λz.(x x) z)) (λx.(f λz.(x x) z)) (Z combinator - call-by-value Y)
exampleZ :: LExp
exampleZ =
  let lamz = Lambda "z" (App (App (Var "x") (Var "x")) (Var "z"))
      z = Lambda "x" (App (Var "f") lamz)
   in Lambda "f" (App z z)

-- | Additional examples:
-- | (Y K) (Y combinator applied to K)
exampleTop :: LExp
exampleTop = App exampleY exampleK

-- | (Y K) I ... I (with i occurrences of I)
exampleTopId :: Int -> LExp
exampleTopId 0 = exampleTop
exampleTopId i = App (exampleTopId (i - 1)) exampleI

-- | (I I) ... (I I) (with i+1 occurrences of (I I))
exampleIdId :: Int -> LExp
exampleIdId 0 = App exampleI exampleI
exampleIdId i = App (exampleIdId (i - 1)) (App exampleI exampleI)

-- -------------------------------------------------------------

-- | Pretty Printers

-- | Format expression in mathematical notation
-- | Lambda abstractions as (λx.s), applications as (s t), and variables as their names
prettyMath :: LExp -> String
prettyMath (Lambda x s) = "(λ" ++ x ++ "." ++ prettyMath s ++ ")"
prettyMath (Var x) = x
prettyMath (App s t) = "(" ++ prettyMath s ++ " " ++ prettyMath t ++ ")"
prettyMath Hole = "[·]"
prettyMath Bot = "⊥"

-- | Print expression in mathematical notation
printPrettyMath :: LExp -> IO ()
printPrettyMath = putStrLn . prettyMath

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
    freshAlphaRenameIt e mappings fresh = (e, fresh)

-- | Useful fresh names for renaming: ["x1", "x2", ...]
names :: [String]
names = ["x" ++ show i | i <- [1 ..]]

-- | Helper function to test the alpha renaming
testfreshAlphaRename :: LExp -> LExp
testfreshAlphaRename e = fst (freshAlphaRename e names)

-- | Performs substitution s[t/x] with appropriate alpha-renaming
-- | For each substitution of x by t, expression t is renamed using fresh names
-- | Returns the pair (s[t/x], fresh') where fresh' are the unused fresh names
substitute :: (Eq var) => var -> LambdaExpr var -> LambdaExpr var -> [var] -> (LambdaExpr var, [var])
substitute x t (Lambda y s) fresh
  | x == y = (Lambda y s, fresh)
  | otherwise =
      let (s', fresh') = substitute x t s fresh
       in (Lambda y s', fresh')
substitute x t (App r s) fresh =
  let (r', fresh') = substitute x t r fresh
      (s', fresh'') = substitute x t s fresh'
   in (App r' s', fresh'')
substitute x t (Var y) fresh
  | x == y = freshAlphaRename t fresh
  | otherwise = (Var y, fresh)
substitute x t Bot fresh = (Bot, fresh)

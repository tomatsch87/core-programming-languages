-- | Haskell implementation of the Church encoding for Lambda calculus
-- | This demonstrates the Turing completeness of Lambda calculus by providing all necessary tools to simulate a Turing machine with the Church encoding
module ChurchEncoding where

-- \| Imports
import Data.List (last)
import LambdaCalculus
  ( LExp,
    LambdaExpr (..),
    freshAlphaRename,
    names,
    prettyMath,
    printPrettyMath,
    substitute,
  )

-- -------------------------------------------------------------

-- | Church Encoding for Booleans

-- | Church encoding for true: λx.λy.x
churchTrue :: LExp
churchTrue = Lambda "x" (Lambda "y" (Var "x"))

-- | Church encoding for false: λx.λy.y
churchFalse :: LExp
churchFalse = Lambda "x" (Lambda "y" (Var "y"))

-- | Logical negation: λp.(p false true)
churchNot :: LExp
churchNot = Lambda "p" (App (App (Var "p") churchFalse) churchTrue)

-- | Logical OR: λp.λq.(p p q)
churchOr :: LExp
churchOr = Lambda "p" (Lambda "q" (App (App (Var "p") (Var "p")) (Var "q")))

-- | Logical AND: λp.λq.(p q p)
churchAnd :: LExp
churchAnd = Lambda "p" (Lambda "q" (App (App (Var "p") (Var "q")) (Var "p")))

-- | Test function for Church Booleans - evaluates logical operations
testChurchBool :: IO ()
testChurchBool = do
  putStrLn $ "not = " ++ prettyMath churchNot
  putStrLn $ "or = " ++ prettyMath churchOr
  putStrLn $ "and = " ++ prettyMath churchAnd
  putStrLn $ "true = " ++ prettyMath churchTrue
  putStrLn $ "false = " ++ prettyMath churchFalse
  sequence_
    [ putStrLn ("Evaluating " ++ op ++ " " ++ arg1)
        >> printTraceToNF (App opC arg1C)
      | (op, opC) <- [("not", churchNot)],
        (arg1, arg1C) <- [("true", churchTrue), ("false", churchFalse)]
    ]
  sequence_
    [ putStrLn ("Evaluating " ++ op ++ " " ++ arg1 ++ " " ++ arg2)
        >> printTraceToNF (App (App opC arg1C) arg2C)
      | (op, opC) <- [("and", churchAnd), ("or", churchOr)],
        (arg1, arg1C) <- [("true", churchTrue), ("false", churchFalse)],
        (arg2, arg2C) <- [("true", churchTrue), ("false", churchFalse)]
    ]

-- -------------------------------------------------------------

-- | Church Encoding for Numbers

-- | Convert a non-negative integer to a Church numeral
-- | 0 is represented as λf.λx.x
-- | n is represented as λf.λx.(f^n x) where f^n means f applied n times
toChurchNumeral :: Int -> LExp
toChurchNumeral 0 = Lambda "f" (Lambda "x" (Var "x"))
toChurchNumeral n = Lambda "f" (Lambda "x" (applyN n (Var "f") (Var "x")))
  where
    -- \| Apply a function n times to an argument
    applyN :: Int -> LExp -> LExp -> LExp
    applyN 0 _ x = x
    applyN count f x = App f (applyN (count - 1) f x)

-- | Addition of Church numerals: λm.λn.λf.λx.(m f (n f x))
churchPlus :: LExp
churchPlus = Lambda "m" (Lambda "n" (Lambda "f" (Lambda "x" (App (App (Var "m") (Var "f")) (App (App (Var "n") (Var "f")) (Var "x"))))))

-- | Successor function: λn.λf.λx.(f (n f x))
churchSucc :: LExp
churchSucc = Lambda "n" (Lambda "f" (Lambda "x" (App (Var "f") (App (App (Var "n") (Var "f")) (Var "x")))))

-- | Predecessor function: λn.λf.λx.(n (λg.λh.(h (g f))) (λz.x) (λu.u))
churchPred :: LExp
churchPred =
  Lambda
    "n"
    ( Lambda
        "f"
        ( Lambda
            "x"
            ( App
                ( App
                    ( App
                        (Var "n")
                        (Lambda "g" (Lambda "h" (App (Var "h") (App (Var "g") (Var "f")))))
                    )
                    (Lambda "z" (Var "x"))
                )
                (Lambda "u" (Var "u"))
            )
        )
    )

-- | Check if a number is zero: λn.(n (λx.false) true)
churchIsZero :: LExp
churchIsZero = Lambda "n" (App (App (Var "n") (Lambda "x" churchFalse)) churchTrue)

-- | Multiplication of Church numerals: λm.λn.λf.λx.(m (n f) x)
churchMult :: LExp
churchMult = Lambda "m" (Lambda "n" (Lambda "f" (Lambda "x" (App (App (Var "m") (App (Var "n") (Var "f"))) (Var "x")))))

-- | Test function for Church numerals - evaluates arithmetic operations
testChurchNumeral :: IO ()
testChurchNumeral = do
  putStrLn "computing 3+5 using the church encoding"
  let n3 = toChurchNumeral 3
  putStrLn $ "Number 3 in Church-Encoding: " ++ prettyMath n3
  let n5 = toChurchNumeral 5
  putStrLn $ "Number 5 in Church-Encoding: " ++ prettyMath n5
  putStrLn $ "Addition in Church-Encoding: " ++ prettyMath churchPlus
  putStrLn "Computing 3+5"
  printTraceToNF $ App (App churchPlus n3) n5
  putStrLn "computing succ 3 using the church encoding"
  printTraceToNF (App churchSucc n3)
  putStrLn "computing pred 3 using the church encoding"
  printTraceToNF (App churchPred n3)
  putStrLn $ "Multiplication in Church-Encoding: " ++ prettyMath churchMult
  putStrLn "Computing 3*5"
  printTraceToNF $ App (App churchMult n3) n5

-- -------------------------------------------------------------

-- | Church Encoding for Pairs

-- | Pair constructor: λx.λy.λz.(z x y)
churchPair :: LExp
churchPair = Lambda "x" (Lambda "y" (Lambda "z" (App (App (Var "z") (Var "x")) (Var "y"))))

-- | First projection: λp.(p λx.λy.x)
churchFirst :: LExp
churchFirst = Lambda "p" (App (Var "p") (Lambda "x" (Lambda "y" (Var "x"))))

-- | Second projection: λp.(p λx.λy.y)
churchSecond :: LExp
churchSecond = Lambda "p" (App (Var "p") (Lambda "x" (Lambda "y" (Var "y"))))

-- | Swap the elements of a pair: λp.(pair (second p) (first p))
churchSwap :: LExp
churchSwap = Lambda "p" (App (App churchPair (App churchSecond (Var "p"))) (App churchFirst (Var "p")))

-- | Test function for Church pairs - demonstrates pair operations
testChurchPair :: IO ()
testChurchPair = do
  let ab = App (App churchPair (Var "a")) (Var "b")
  let cd = App (App churchPair (Var "c")) (Var "d")
  putStrLn $ "(a,b) in Church-Encoding: " ++ prettyMath ab
  putStrLn "Normalform of (a,b) in Church-Encoding: "
  printNF ab
  putStrLn $ "(c,d) in Church-Encoding: " ++ prettyMath cd
  putStrLn "Normalform of (c,d) in Church-Encoding: "
  printNF cd
  let abcd = App (App churchPair ab) cd
  putStrLn $ "((a,b),(c,d)) in Church-Encoding: " ++ prettyMath abcd
  putStrLn "Normalform of ((a,b),(c,d)) in Church-Encoding: "
  printNF abcd
  putStrLn $ "fst in Church-Encoding: " ++ prettyMath churchFirst
  let e1 = App churchFirst (App churchFirst abcd)
  let e2 = App churchFirst (App churchSecond abcd)
  let e3 = App churchSecond (App churchFirst abcd)
  let e4 = App churchSecond (App churchSecond abcd)
  putStrLn "computing (fst (fst ((a,b),(c,d)))"
  printTraceToNF e1
  putStrLn "computing (snd (fst ((a,b),(c,d)))"
  printTraceToNF e3
  putStrLn "computing (fst (snd ((a,b),(c,d)))"
  printTraceToNF e2
  putStrLn "computing (snd (snd ((a,b),(c,d)))"
  printTraceToNF e4
  putStrLn "computing swap (a,b)"
  printTraceToNF (App churchSwap ab)

-- -------------------------------------------------------------

-- | Church Encoding for Lists

-- | Empty list: (pair true true)
churchNil :: LExp
churchNil = App (App churchPair churchTrue) churchTrue

-- | List constructor: λh.λt.(pair false (pair h t))
churchCons :: LExp
churchCons = Lambda "h" (Lambda "t" (App (App churchPair churchFalse) (App (App churchPair (Var "h")) (Var "t"))))

-- | Check if list is empty: first
isChurchNil :: LExp
isChurchNil = churchFirst

-- | Get the head of a list: λl.(first (second l))
churchHead :: LExp
churchHead = Lambda "l" (App churchFirst (App churchSecond (Var "l")))

-- | Get the tail of a list: λl.(second (second l))
churchTail :: LExp
churchTail = Lambda "l" (App churchSecond (App churchSecond (Var "l")))

-- | Compute the last element of a list
-- | Normal in Haskell would be:
-- | last xs  = if  null (tail xs) then  head xs else last (tail xs)
-- | The recursion can be expressed in the lambda calculus using the Y combinator
-- | We achieve this by applying the Y combinator to a function that takes a function as an argument
-- | and returns a function that takes a list as an argument and returns the last element of the list
churchLast = App exampleY churchLastF

exampleY =
  let y = Lambda "x" (App (Var "f") (App (Var "x") (Var "x")))
   in Lambda "f" (App y y)

-- | λf.λl.((isNil (tail l)) (head l) (f (tail l)))
churchLastF =
  Lambda
    "f"
    ( Lambda
        "l"
        ( App
            ( App
                (App isChurchNil (App churchTail (Var "l")))
                (App churchHead (Var "l"))
            )
            (App (Var "f") (App churchTail (Var "l")))
        )
    )

-- | Test function for Church lists - demonstrates list operations
testChurchList :: IO ()
testChurchList = do
  let abc = App (App churchCons (Var "a")) (App (App churchCons (Var "b")) (App (App churchCons (Var "c")) churchNil))
  putStrLn $ "[a,b,c] in Church-Encoding: " ++ prettyMath abc
  putStrLn "Normalform of [a,b,c] in Church-Encoding: "
  printTraceToNF abc
  putStrLn "computing (head [a,b,c]):"
  printNF (App churchHead abc)
  putStrLn "computing (head (tail [a,b,c])):"
  printNF (App churchHead (App churchTail abc))
  putStrLn "computing last [a,b,c]:"
  printNF (App churchLast abc)

-- -------------------------------------------------------------

-- | Evaluation Functions

-- | Performs one step of deep beta reduction
oneDeepBeta :: (Eq var) => LambdaExpr var -> [var] -> Maybe (LambdaExpr var, [var])
oneDeepBeta (Var _) _ = Nothing
oneDeepBeta (Lambda x s) fresh =
  case oneDeepBeta s fresh of
    Nothing -> Nothing
    Just (s', fresh') -> Just (Lambda x s', fresh')
oneDeepBeta (App (Lambda x s) t) fresh =
  Just $ substitute x t s fresh
oneDeepBeta (App s t) fresh =
  case oneDeepBeta s fresh of
    Nothing -> case oneDeepBeta t fresh of
      Nothing -> Nothing
      Just (t', fresh') -> Just (App s t', fresh')
    Just (s', fresh') -> Just (App s' t, fresh')

-- | Traces the evaluation to normal form
traceToNF :: (Eq var) => LambdaExpr var -> [var] -> [LambdaExpr var]
traceToNF e fresh = case oneDeepBeta e fresh of
  Just (e', fresh') -> e : traceToNF e' fresh'
  Nothing -> [e]

-- | Computes the normal form of an expression
toNF :: (Eq var) => LambdaExpr var -> [var] -> LambdaExpr var
toNF e fresh = last $ traceToNF e fresh

-- | Prints the normal form of an expression
printNF :: LExp -> IO ()
printNF e =
  let (e', fresh) = freshAlphaRename e names
      e'' = toNF e' fresh
   in printPrettyMath e''

-- | Prints the trace of evaluation steps to normal form
printTraceToNF :: LExp -> IO ()
printTraceToNF e =
  let (e', fresh) = freshAlphaRename e names
      expressions = map prettyMath (traceToNF e' fresh)
   in putStrLn $ unlines $ ("      " ++ head expressions) : map ("-C,β> " ++) (tail expressions)

-- | Prints a limited number of steps in the evaluation trace
printTraceToNFLimit :: LExp -> Int -> IO ()
printTraceToNFLimit e l =
  let (e', fresh) = freshAlphaRename e names
      expressions = map prettyMath (take l $ traceToNF e' fresh)
   in putStrLn $ unlines $ ("      " ++ head expressions) : map ("-C,β> " ++) (tail expressions)
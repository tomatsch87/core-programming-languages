-- | IMP represents a simple imperative programming language.
-- | It classifies as a "while" language and is Turing complete.
module IMP where

-- \| Imports
import Data.List hiding (lookup)
import Data.Map qualified as Map
import Prelude hiding (lookup)

-- -------------------------------------------------------------

-- | State Representation

-- | Represents a program state as a mapping from variable names to integer values
newtype State = State (Map.Map String Integer)

-- | Lookup a variable's value in the state
-- | Returns Nothing if the variable is not defined
lookup :: String -> State -> Maybe Integer
lookup key (State st) = Map.lookup key st

-- | Store a value for a variable in the state
-- | Creates a new binding or updates an existing one
store :: String -> Integer -> State -> State
store key val (State st) = State (Map.insert key val st)

-- | Create an empty state with no bindings
empty :: State
empty = State Map.empty

-- | Show instance for State to display variable bindings
instance Show State where
  show (State st) = "{" ++ intercalate "," (map (\(k, v) -> k ++ " -> " ++ show v) (Map.assocs st)) ++ "}"

-- -------------------------------------------------------------

-- | Arithmetic Expressions

-- | Represents arithmetic expressions in the IMP language
data AExp
  = Num Integer -- Integer literal
  | Loc String -- Variable reference
  | AExp :+: AExp -- Addition
  | AExp :-: AExp -- Subtraction
  | AExp :*: AExp -- Multiplication
  deriving (Eq, Show)

-- | Evaluate an arithmetic expression in a given state
-- | evalA e σ = n corresponds to <e,σ>↓n in the Big-Step-Semantics
evalA :: AExp -> State -> Integer
evalA expr state = case expr of
  Num i -> i
  Loc s -> case lookup s state of
    Just val -> val
    Nothing -> error $ "Variable " ++ s ++ " not initialized"
  a1 :+: a2 -> evalA a1 state + evalA a2 state
  a1 :-: a2 -> evalA a1 state - evalA a2 state
  a1 :*: a2 -> evalA a1 state * evalA a2 state

-- -------------------------------------------------------------

-- | Boolean Expressions

-- | Represents boolean expressions in the IMP language
data BExp
  = TRUE -- Boolean true constant
  | FALSE -- Boolean false constant
  | AExp :==: AExp -- Equality comparison
  | AExp :<=: AExp -- Less than or equal comparison
  | Not BExp -- Logical negation
  | BExp :&&: BExp -- Logical AND
  | BExp :||: BExp -- Logical OR
  deriving (Eq, Show)

-- | Evaluate a boolean expression in a given state
-- | evalB e σ = b corresponds to <e,σ>↓b in the Big-Step-Semantics
evalB :: BExp -> State -> Bool
evalB expr state = case expr of
  TRUE -> True
  FALSE -> False
  a1 :==: a2 -> evalA a1 state == evalA a2 state
  a1 :<=: a2 -> evalA a1 state <= evalA a2 state
  Not b -> not (evalB b state)
  b1 :&&: b2 -> evalB b1 state && evalB b2 state
  b1 :||: b2 -> evalB b1 state || evalB b2 state

-- -------------------------------------------------------------

-- | Commands

-- | Represents commands (statements) in the IMP language
data Cmd
  = Skip -- No-operation command
  | String :=: AExp -- Assignment command (var := expr)
  | Seq Cmd Cmd -- Sequential composition (c1; c2)
  | ITE BExp Cmd Cmd -- If-Then-Else command
  | WHDO BExp Cmd -- While-Do loop command
  deriving (Eq, Show)

-- | Evaluate a command in a given state, producing a new state
-- | eval c σ₁ = σ₂ corresponds to <c,σ₁>↓σ₂ in the Big-Step-Semantics
eval :: Cmd -> State -> State
eval cmd state = case cmd of
  Skip -> state
  var :=: a -> store var (evalA a state) state
  Seq c1 c2 -> eval c2 (eval c1 state)
  ITE b c1 c2 ->
    if evalB b state
      then eval c1 state
      else eval c2 state
  WHDO b c ->
    if evalB b state
      then
        let state' = eval c state
         in eval (WHDO b c) state'
      else state

-- -------------------------------------------------------------

-- | Examples

-- | Main function with example programs
main :: IO ()
main = do
  -- Example 1: Infinite loop (not executed due to Haskell's laziness)
  let p1 = WHDO TRUE Skip
  print p1

  -- Example 2: Count down from x to 0, adding 2 to y each time
  let p2 =
        WHDO
          (Num 1 :<=: Loc "x")
          ( Seq
              ("y" :=: (Loc "y" :+: Num 2))
              ("x" :=: (Loc "x" :-: Num 1))
          )
  print p2

  -- Execute example 2 with initial state {x -> 50, y -> 0}
  let state = store "y" 0 $ store "x" 50 empty
  putStrLn $ "Before: " ++ show state
  putStrLn $ "After: " ++ show (eval p2 state)

{-
Expected output:

WHDO TRUE Skip
WHDO (Num 1 :<=: Loc "x") (Seq ("y" :=: (Loc "y" :+: Num 2)) ("x" :=: (Loc "x" :-: Num 1)))
Before: {x -> 50,y -> 0}
After: {x -> 0,y -> 100}
-}
-- \| A Turing machine simulator in Haskell
import Data.List
import Data.Maybe

-- -------------------------------------------------------------

-- | Data types

-- | Represents the movement direction of the read/write head
data Move = MLeft | MRight | MNothing
  deriving (Eq, Show)

-- | Represents a Turing machine.
-- The TM is polymorphic over the tape alphabet and states.
-- Components:
--  * start: Initial state of the TM
--  * accepting: Set of accepting states
--  * delta: Transition function
--
-- Note: Alphabets and states are represented implicitly.
-- The blank symbol is represented using Maybe:
--  * Nothing - represents a blank symbol
--  * Just s  - represents the symbol s from the alphabet
data TM alphabet state
  = TM
  { start :: state,
    accepting :: [state],
    -- | Transition function: receives current state and symbol,
    --   returns new state, new symbol, and head movement direction
    delta :: (state, Maybe alphabet) -> (state, Maybe alphabet, Move)
  }

-- | Represents a configuration of a Turing machine during execution
-- * The current tape content is: before ++ [current] ++ after
-- * The read/write head is positioned at 'current'
-- * 'currState' is the current state of the machine
data TMConfig alphabet state
  = TMConfig
  { before :: [Maybe alphabet], -- Symbols to the left of head
    current :: Maybe alphabet, -- Symbol under the head
    after :: [Maybe alphabet], -- Symbols to the right of head
    currState :: state -- Current state
  }
  deriving (Eq, Show)

-- -------------------------------------------------------------

-- | Functions

-- | Calculates one step of the Turing machine execution
-- Returns:
--  * Nothing - if machine is in an accepting state
--  * Just config - the configuration after performing one step
oneStep :: (Eq s) => TM a s -> TMConfig a s -> Maybe (TMConfig a s)
oneStep tm tc
  -- If already in an accepting state, halt execution
  | currState tc `elem` accepting tm = Nothing
  -- Otherwise, compute the next configuration
  | otherwise =
      case delta tm (currState tc, current tc) of
        (s', a', m) ->
          -- Apply transition based on movement direction
          case m of
            -- No movement, just update state and symbol
            MNothing -> Just $ tc {currState = s', current = a'}
            -- Move right
            MRight ->
              if null (after tc)
                then
                  -- At right edge - extend with blank
                  Just $
                    tc
                      { currState = s',
                        current = Nothing,
                        before = before tc ++ [a'],
                        after = []
                      }
                else
                  -- Move head right
                  Just $
                    tc
                      { currState = s',
                        current = head (after tc),
                        before = before tc ++ [a'],
                        after = tail (after tc)
                      }
            -- Move left
            MLeft ->
              if null (before tc)
                then
                  error "move left on start position"
                else
                  if null (after tc) && isNothing a'
                    then
                      Just $
                        tc
                          { currState = s',
                            current = last (before tc),
                            before = init (before tc),
                            after = []
                          }
                    else
                      Just $
                        tc
                          { currState = s',
                            current = last (before tc),
                            before = init (before tc),
                            after = a' : after tc
                          }

-- | Runs a Turing machine to completion on given input
-- Returns the final configuration if the machine halts in an accepting state
runMachine tm input =
  let startconfig =
        TMConfig
          { current = head input,
            before = [],
            after = tail input,
            currState = start tm
          }
      go tc = maybe tc go (oneStep tm tc)
   in go startconfig

-- | Tests if a Turing machine accepts the given input
-- Returns True if the machine reaches an accepting state
tmEncode tm input = case runMachine tm input of
  (TMConfig {}) -> True

-- -------------------------------------------------------------

-- | Example

-- | Example TM that searches for the last symbol of the input
ex1 =
  let d (1, Just 0) = (1, Just 0, MRight)
      d (1, Just 1) = (1, Just 1, MRight)
      d (1, Nothing) = (2, Nothing, MLeft)
      d (2, _) = undefined
      input = [Just 0, Just 1, Just 0, Nothing]
      tm =
        TM
          { delta = d,
            accepting = [2],
            start = 1
          }
   in runMachine tm input

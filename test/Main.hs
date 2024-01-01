module Main where

-- base
import Control.Monad (forM_, guard, when)
import Data.Maybe (fromMaybe, listToMaybe)
import Data.String (IsString)

-- text
import Data.Text (Text)

-- scientific
import Data.Scientific (Scientific)

-- sop-core
import Data.SOP

-- optimal-lp
import Optimal

newtype Student = Student {getStudent :: Text}
  deriving (IsString, Show, Eq, Ord) -- This doesn't hide the constructor sufficiently

instance Varnameable Student where
  varname = getStudent

newtype Topic = Topic {getTopic :: Text}
  deriving (IsString, Show, Eq, Ord)

instance Varnameable Topic where
  varname = getTopic

students :: [Student]
students = ["alice", "bob", "charlotte", "daniel"]

topics :: [Topic]
topics = ["X", "Y"]

votes :: [(Student, Topic, Scientific)]
votes =
  [ ("alice", "X", 4)
  , ("bob", "X", 4)
  , ("bob", "Y", 2)
  , ("charlotte", "X", 3)
  , ("charlotte", "Y", 3)
  , ("daniel", "X", 1)
  ]

-- "Some monad tutorials start with Maybe, some with Lists. Does it matter? I hope not, I found functions to convert one into the other"
lookupVote :: Student -> Topic -> Maybe Scientific
lookupVote student topic = listToMaybe $ do
  (currentStudent, currentTopic, vote) <- votes
  guard $ student == currentStudent
  guard $ topic == currentTopic
  pure vote

lookupVote0 :: Student -> Topic -> Scientific
lookupVote0 student topic = fromMaybe 0 $ lookupVote student topic

capacity :: Topic -> Integer
capacity "X" = 2
capacity "Y" = 2

problem :: OptiM '[Student, Topic] (LpOptimizedValue (Finite Student -> Finite Topic))
problem = do
  -- FIXME I should have fmap for LpOptimizedValue
  topicOf <- optimal @_ @(Finite Student -> Finite Topic)
  forEvery @Student $ \student -> better $ (lookupVote0 (getFinite student) . getFinite) <$$> topicOf $$ student
  forEvery @Topic $ \(Finite topic) -> LpSize (LpPreimage topicOf (Finite topic)) <=! capacity topic
  return topicOf

{-
Ways to make it more complex:
* sort topics into rooms and/or times
* sort teachers into topics
* optimize teachers, then optimize students again with fixed teachers
* find minimal set of constraints that need to be relaxed to make it feasible
* only take sorted preferences into account, not cardinalities
* optimize minimum student happiness
-}

-- problem2 :: OptiM '[Student, Topic] (LpOptimizedValue (FiniteType Student :~> FiniteType Topic), LpOptimizedValue (FiniteType Student))
-- problem2 = do
--   topicOf <- optimalFunction @Student @Topic "topicOf"
--   forEvery @Topic $ \topic -> LpSize (LpPreimage topicOf topic) <=! capacity topic
--   minimalStudent <- optimal @Student "minimalStudent"
--   forEvery @Student $ \student -> (lookupVote0 <$$> minimalStudent) <$$> (topicOf <$$> minimalStudent) <=! lookupVote0 student <$$> topicOf $$ student
--   return (topicOf, minimalStudent)

main :: IO ()
main = do
  putStrLn "First problem"
  putStrLn "-------------"
  topicOf <- runOptiM problem $ students :* topics :* Nil -- FIXME nicer constructors for this list
  let optimalAssignment = [("alice", "X"), ("bob", "X"), ("charlotte", "Y"), ("daniel", "Y")]
  forM_ students $ \student -> do
    print (student, topicOf $ Finite student)
    when (lookup student optimalAssignment /= Just (getFinite $ topicOf $ Finite student)) $ error "Ooops!"

  -- putStrLn "--------------"
  -- putStrLn "Second problem"
  -- putStrLn "--------------"
  -- (topicOf, minimalStudent) <- runOptiM problem2 $ students :* topics :* Nil -- FIXME nicer constructors for this list
  -- print (minimalStudent, topicOf minimalStudent)
  -- forM_ students $ \student -> print (student, topicOf student)

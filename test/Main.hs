module Main where

-- base
import Control.Monad (forM_, guard)
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

capacity :: Topic -> Integer
capacity "X" = 2
capacity "Y" = 2

problem :: OptiM '[Student, Topic] (LpOptimizedValue (FiniteType Student :~> FiniteType Topic))
problem = do
  topicOf <- optimalFunction @Student @Topic "topicOf"
  forEvery @Student $ \student -> better $ LpFmap (fromMaybe 0 . lookupVote student) $ topicOf $$ student
  forEvery @Topic $ \topic -> LpSize (LpPreimage topicOf topic) <=! capacity topic
  return topicOf

main :: IO ()
main = do
  topicOf <- runOptiM problem $ students :* topics :* Nil -- FIXME nicer constructors for this list
  forM_ students $ \student -> print (student, topicOf student)

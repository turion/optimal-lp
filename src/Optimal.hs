{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeOperators #-}

module Optimal where

-- base
import Control.Monad (forM, forM_)
import Control.Monad.Trans.Class (lift)
import Data.Kind hiding (Constraint)
import Data.Maybe (fromMaybe)
import Data.Monoid (Sum (getSum))
import Data.Semigroup (Arg (..))

-- transformers
import Control.Monad.Trans.Accum (AccumT, add, evalAccumT, look)
import Control.Monad.Trans.Reader (Reader, asks, runReader)
import Control.Monad.Trans.Writer.CPS (WriterT, runWriterT, writer) -- FIXME performance?

-- text
import Data.Text hiding (concat, head, singleton)

-- containers
import Data.Map (Map, argSet, elems, filter, fromList, fromSet, intersectionWith, keys, keysSet, lookup, mapKeys, null, restrictKeys, toAscList, toList, unions, (!))
import Data.Set

-- sop-core
import Data.SOP

-- -- glpk-hs
-- import Control.Monad.LPMonad
-- import Data.LinearProgram.GLPK.Solver

-- scientific
import Data.Scientific

-- MIP
import Numeric.Optimization.MIP hiding (Constraint, Finite, constraints, name, variables, vars)
import Numeric.Optimization.MIP qualified as MIP
import Numeric.Optimization.MIP.Solver (SolveOptions (solveErrorLogger, solveLogger), solve)
import Numeric.Optimization.MIP.Solver.Glpsol

-- FIXME make a transformer
newtype OptiM (ranges :: [Type]) a = OptiM {getOptiM :: AccumT (Sum Int) (WriterT LpDeclarations (Reader (NP [] ranges))) a}
  deriving (Functor, Applicative, Monad)

freshIndex :: OptiM ranges Text
freshIndex = OptiM $ do
  i <- look
  add 1
  return $ pack $ show $ getSum i

myWriter :: (a, LpDeclarations) -> OptiM ranges a
myWriter = OptiM . lift . writer

myTell :: LpDeclarations -> OptiM ranges ()
myTell = myWriter . pure

myAsks :: (NP [] ranges -> a) -> OptiM ranges a
myAsks = OptiM . lift . lift . asks

{-
instance Monad (OptiM ranges) where
  OptiM ma >>= f = OptiM $ writer $ reader $ \(ranges, assignments) ->
    let
      (readerA, wA) = runWriter ma
      a = runReader readerA r
      (readerB, wB) = runWriter $ f a
      b = runReader readerB r
    in (b, wA <> wB)
-}

data LpType = LpInteger (Maybe Integer) (Maybe Integer) | LpFloat (Maybe Scientific) (Maybe Scientific)
  deriving (Eq, Ord)

data Variable = Variable
  { name :: Text
  , lpType :: LpType -- FIXME make this type level later?
  }
  deriving (Eq, Ord)

declareVariable :: Variable -> OptiM ranges ()
declareVariable var = myTell mempty{variablesDeclared = singleton var}

addConstraint :: Constraint -> OptiM ranges ()
addConstraint constraint = myTell mempty{constraintsDeclared = singleton constraint}

data LpLiteral = IntegerLiteral Integer | FloatLiteral Scientific
  deriving (Eq, Ord)

data LpValue = VariableValue Variable LpLiteral | LiteralValue LpLiteral
  deriving (Eq, Ord)

data Constraint
  = LEQ
      { smaller :: Set LpValue
      , bigger :: Set LpValue
      }
  | Equal
      { lhs :: Set LpValue
      , rhs :: Set LpValue
      }
  deriving (Eq, Ord)

data LpDeclarations = LpDeclarations
  { variablesDeclared :: Set Variable
  , constraintsDeclared :: Set Constraint
  , objective :: Set LpValue
  }

-- FIXME how do you derive this again
instance Semigroup LpDeclarations where
  LpDeclarations v1 c1 o1 <> LpDeclarations v2 c2 o2 = LpDeclarations (v1 <> v2) (c1 <> c2) (o1 <> o2)
instance Monoid LpDeclarations where
  mempty = LpDeclarations mempty mempty mempty

data LpAssignment = LpAssignment
  { variableAssigned :: Variable
  , resultAssigned :: LpLiteral
  }
  deriving (Eq, Ord)

-- FIXME also a class "IsIntegerVector"

data LpOptimizedValue a where
  LpOptimizedIntegerValue :: Variable -> LpOptimizedValue Integer
  LpOptimizedFloatValue :: Variable -> LpOptimizedValue Scientific
  LpOptimizedFunction :: (Ord a) => Map a (Map Variable b) -> LpOptimizedValue (a -> b)
  -- LpOptimizedRelation :: LpOptimizedValue a -> LpOptimizedValue b -> LpOptimizedValue (Set (a, b))
  LpApplication :: LpOptimizedValue (a -> b) -> a -> LpOptimizedValue b -- FIXME restrictive: Want to apply an arbitrary LpOptimizedValue
  LpOptimizedFinite :: Map Variable a -> LpOptimizedValue a
  -- LpOptimizedSetValue :: Set (LpOptimizedValue a) -> LpOptimizedValue (Set a)
  LpPreimage :: (Eq b) => LpOptimizedValue (a -> b) -> b -> LpOptimizedValue (Set a) -- FIXME restrictive: Want to apply an arbitrary LpOptimizedValue
  LpSize :: LpOptimizedValue (Set a) -> LpOptimizedValue Integer
  LpFmap :: (a -> Scientific) -> LpOptimizedValue a -> LpOptimizedValue Scientific

infixl 7 $$

($$) :: LpOptimizedValue (a -> b) -> a -> LpOptimizedValue b
($$) = LpApplication

infixl 5 <$$>

(<$$>) :: (a -> Scientific) -> LpOptimizedValue a -> LpOptimizedValue Scientific
(<$$>) = LpFmap

-- LpRelatedL :: LpOptimizedValue (a :<~> b) -> LpOptimizedValue a -> LpOptimizedValue b
-- LpRelatedR :: LpOptimizedValue (a :<~> b) -> LpOptimizedValue b -> LpOptimizedValue a

-- FIXME maybe this can profit from an intermediate step where I just resolve the value to variables
recoverDecoded :: LpOptimizedValue a -> Reader (Map Variable LpLiteral) a
recoverDecoded (LpOptimizedIntegerValue var) = asks $ \assignments ->
  maybe
    (error "recoverDecoded: integer var not among assignments")
    (\(IntegerLiteral i) -> i)
    $ Data.Map.lookup var assignments
recoverDecoded (LpOptimizedFloatValue var) = asks $ \assignments ->
  maybe
    (error "recoverDecoded: float var not among assignments")
    (\(FloatLiteral f) -> f)
    $ Data.Map.lookup var assignments
recoverDecoded (LpOptimizedFunction varMap) = asks $ \assignments a ->
  flip runReader assignments
    $ recoverDecoded
    $ LpOptimizedFinite
    $ fromMaybe (error "recoverDecoded: value not in map")
    $ Data.Map.lookup a varMap
recoverDecoded (LpApplication fun a) = do
  f <- recoverDecoded fun
  pure $ f a
recoverDecoded (LpOptimizedFinite vars) = asks $ \assignments ->
  let assignmentsOfThisType = Data.Map.intersectionWith (,) assignments vars
      ones = Data.Map.toList $ Data.Map.filter (\(lit, _) -> lit == IntegerLiteral 1) assignmentsOfThisType
   in case ones of
        [(_, (_, a))] -> a
        [] -> error "recoverDecoded: No value was selected"
        _ -> error "recoverDecoded: Multiple values were selected"
recoverDecoded (LpPreimage (LpOptimizedFunction varMap) b) = asks $ \assignments ->
  keysSet $ not . Data.Map.null . Data.Map.filter (== IntegerLiteral 1) . restrictKeys assignments . keysSet . Data.Map.filter (== b) <$> varMap
recoverDecoded (LpPreimage (LpApplication _f _a) _target) = error "recoverDecoded: Not yet implemented"
recoverDecoded (LpSize set) = fromIntegral . Data.Set.size <$> recoverDecoded set
recoverDecoded (LpFmap f (LpApplication (LpOptimizedFunction varMap) a)) = asks $ \assignments ->
  sum $ intersectionWith ((*) . literalToScientific) assignments $ fmap f $ varMap ! a
recoverDecoded (LpFmap _ _) = error "recoverDecoded: LpFmap: Not yet implemented"

class Varnameable a where
  varname :: a -> Text

class (Varnameable (Specify a), Varnameable (ConstrainOn a)) => Optimal ranges a where
  -- FIXME maybe also require an example for feasibility?
  type ConstrainOn a :: Type
  type Specify a :: Type
  optimal :: OptiM ranges (LpOptimizedValue a)
  optimal = do
    let proxy = Proxy @a
    i <- freshIndex
    constrainOns <- constrainVars proxy
    varsAndValues <- forM constrainOns $ \constrainOn -> do
      specified <- names proxy constrainOn
      let varsAndValues = Data.Map.fromList $ (\a -> (Variable{name = "var_" <> varname constrainOn <> "_" <> varname a <> "_" <> i, lpType = LpInteger (Just 0) (Just 1)}, a)) <$> specified
          vars = keys varsAndValues
      forM_ vars declareVariable
      mapM_ addConstraint =<< constraints proxy constrainOn vars
      return (constrainOn, varsAndValues)
    value proxy varsAndValues
  example :: OptiM ranges a
  constrainVars :: Proxy a -> OptiM ranges [ConstrainOn a]
  names :: Proxy a -> ConstrainOn a -> OptiM ranges [Specify a]
  constraints :: Proxy a -> ConstrainOn a -> [Variable] -> OptiM ranges [Constraint]
  value :: Proxy a -> [(ConstrainOn a, Map Variable (Specify a))] -> OptiM ranges (LpOptimizedValue a)

newtype Finite a = Finite {getFinite :: a}
  deriving (Show)

instance (Varnameable a) => Varnameable (Finite a) where
  varname = varname . getFinite

instance Varnameable () where
  varname () = "unit"

class FiniteIn ranges a where
  listAll :: OptiM ranges [a]

instance Contains a ranges => FiniteIn ranges (Finite a) where
  listAll = myAsks $ fmap Finite . extract

instance forall a ranges. (Contains a ranges, Varnameable a) => Optimal ranges (Finite a) where
  type ConstrainOn (Finite a) = ()
  type Specify (Finite a) = a

  example = myAsks $ head . fmap Finite . extract
  constrainVars _ = pure [()]
  names _ () = myAsks $ extract @a
  constraints _ () vars =
    pure
      [ LEQ
          { smaller = Data.Set.fromList $ flip VariableValue (IntegerLiteral 1) <$> vars
          , bigger = singleton (LiteralValue (IntegerLiteral 1))
          }
      ]
  value _ = return . LpOptimizedFinite . Data.Map.unions . fmap (fmap Finite . snd)


-- FIXME What repetition can be avoided when comparing with optimal? Can I maybe make a type class?
optimalFunction ::
  forall a b ranges.
  (Contains a ranges, Contains b ranges, Ord a, Varnameable a, Varnameable b) =>
  OptiM ranges (LpOptimizedValue (a -> b))
optimalFunction = do
  name <- freshIndex
  as <- myAsks (extract @a)
  bs <- myAsks (extract @b)
  let varsAndValues =
        Data.Map.fromList
          $ ( \a ->
                ( a
                , Data.Map.fromList
                    $ (\b -> (Variable{name = varname a <> "_" <> varname b <> "_" <> name, lpType = LpInteger (Just 0) (Just 1)}, b))
                    <$> bs
                )
            )
          <$> as
      vars = concat $ Data.Map.elems $ keys <$> varsAndValues
  forM_ as $ \a -> do
    let Just mapB = Data.Map.lookup a varsAndValues
        vars = keys mapB
    forM_ vars declareVariable
    addConstraint
      Equal
        { lhs = Data.Set.fromList $ flip VariableValue (IntegerLiteral 1) <$> vars
        , rhs = singleton (LiteralValue (IntegerLiteral 1))
        }
  return $ LpOptimizedFunction varsAndValues

infix 4 <=!

-- FIXME naming: "constrainable"? or something else?
class LpComparable a b where
  (<=!) :: a -> b -> OptiM ranges ()

instance LpComparable (LpOptimizedValue Integer) Integer where
  (LpSize (LpPreimage (LpOptimizedFunction varMap) b)) <=! i = do
    addConstraint
      LEQ
        { -- FIXME it's annoying with the factor 1 here and there, this should not be necessary
          smaller = Data.Set.unions $ Data.Map.elems $ fmap (keysSet . Data.Map.mapKeys (`VariableValue` IntegerLiteral 1)) $ Data.Map.filter (== b) <$> varMap
        , bigger = singleton (LiteralValue (IntegerLiteral i))
        }
  _ <=! _ = error "<=!: Not yet implemented"

instance LpComparable (LpOptimizedValue Scientific) (LpOptimizedValue Scientific) where
  LpFmap f (LpOptimizedFinite x) <=! LpFmap g (LpApplication (LpOptimizedFunction h) y) =
    addConstraint
      LEQ
        { smaller = Data.Set.map (\(Arg var val) -> VariableValue var (FloatLiteral val)) $ Data.Map.argSet $ f <$> x
        , bigger = Data.Set.map (\(Arg var val) -> VariableValue var (FloatLiteral val)) $ Data.Map.argSet $ g <$> h ! y
        }
  -- \$ do
  --   (var, a) <- Data.Map.toList x
  --   (var', b) <- Data.Map.toList $ h ! y
  --   _
  _ <=! _ = error "<=!: Not yet implemented"

(<=!!) :: LpValue -> LpValue -> OptiM ranges ()
smaller <=!! bigger =
  addConstraint
    LEQ
      { smaller = singleton smaller
      , bigger = singleton bigger
      }

forEvery :: (Contains a ranges) => (a -> OptiM ranges b) -> OptiM ranges ()
forEvery f = do
  as <- myAsks extract
  forM_ as f

class Contains a ranges where
  extract :: NP f ranges -> f a

instance {-# OVERLAPPING #-} Contains a (a ': ranges) where
  extract = hd

instance {-# OVERLAPPABLE #-} (Contains a ranges) => Contains a (b ': ranges) where
  extract = extract . tl

-- FIXME Need a way to just extract the variables from an optimized value. What am I duplicating in comparison with recoverDecoded?
better :: LpOptimizedValue Scientific -> OptiM ranges ()
better (LpFmap f (LpApplication (LpOptimizedFunction varMap) a)) =
  myTell
    $ mempty
      { objective = Data.Set.fromList $ fmap (uncurry VariableValue) $ Data.Map.toList $ fmap (FloatLiteral . f) $ varMap ! a
      }
better _ = error "better: Not yet implemented"

better' :: LpValue -> OptiM ranges ()
better' value = myTell $ mempty{objective = singleton value}

runOptiM :: OptiM ranges (LpOptimizedValue a) -> NP [] ranges -> IO a
runOptiM (OptiM ma) ranges = do
  let (a, declarations) = runReader (runWriterT $ evalAccumT ma 0) ranges
  let problem = mkProblem declarations
  result <- runLp declarations problem -- FIXME maybe this should return a map right away
  return $ runReader (recoverDecoded a) $ Data.Map.mapKeys variableAssigned $ Data.Map.fromSet resultAssigned result

mkProblem :: LpDeclarations -> Problem Scientific
mkProblem
  LpDeclarations
    { variablesDeclared
    , constraintsDeclared
    , objective
    } =
    def
      { varType = mapKeys (toVar . unpack . name) $ fromSet (\Variable{lpType} -> lpTypeToVarType lpType) variablesDeclared
      , varBounds = mapKeys (toVar . unpack . name) $ fromSet (\Variable{lpType} -> lpTypeToBounds lpType) variablesDeclared
      , MIP.constraints = constraintToMIP <$> Data.Set.toList constraintsDeclared -- FIXME Can use SOSConstraints maybe to speed up the problem?
      , objectiveFunction =
          ObjectiveFunction
            { objLabel = Nothing
            , objDir = OptMax
            , objExpr = lpValuesToExpr objective
            }
      }

constraintToMIP :: Constraint -> MIP.Constraint Scientific
constraintToMIP LEQ{smaller, bigger} = lpValuesToExpr smaller .<=. lpValuesToExpr bigger
constraintToMIP Equal{lhs, rhs} = lpValuesToExpr lhs .==. lpValuesToExpr rhs

-- MIP.Constraint
--   { constrLabel = Nothing -- FIXME should be able to supply one
--   , constrIndicator = Nothing -- FIXME what's this??
--   , constrExpr = _
--   , constrLB = _
--   , constrUB = _
--   , constrIsLazy = _
--   }

lpValuesToExpr :: Set LpValue -> Expr Scientific
lpValuesToExpr = sum . fmap lpValueToExpr . Data.Set.toList

lpValueToExpr :: LpValue -> Expr Scientific
-- FIXME these text transformations because of Var and Variables should be unified
lpValueToExpr (VariableValue variable literal) = varExpr (toVar $ unpack variable.name) * constExpr (literalToScientific literal)
lpValueToExpr (LiteralValue literal) = constExpr $ literalToScientific literal

literalToScientific :: LpLiteral -> Scientific
literalToScientific (IntegerLiteral i) = fromIntegral i
literalToScientific (FloatLiteral f) = f

lpTypeToBounds :: LpType -> Bounds Scientific
lpTypeToBounds (LpInteger lowerBound upperBound) = (maybe NegInf fromInteger lowerBound, maybe PosInf fromInteger upperBound)
lpTypeToBounds (LpFloat lowerBound upperBound) = (maybe NegInf MIP.Finite lowerBound, maybe PosInf MIP.Finite upperBound)

lpTypeToVarType :: LpType -> VarType
lpTypeToVarType (LpInteger _ _) = IntegerVariable
lpTypeToVarType (LpFloat _ _) = ContinuousVariable

runLp :: LpDeclarations -> Problem Scientific -> IO (Set LpAssignment)
runLp LpDeclarations{variablesDeclared} problem = do
  putStrLn "Problem:"
  print problem
  Solution
    { solStatus = StatusOptimal
    , solVariables
    } <-
    solve
      glpsol
      def{solveErrorLogger = putStrLn, solveLogger = putStrLn}
      problem
  return $ Data.Set.fromAscList $ uncurry (solVarToLpAssignment variablesDeclared) <$> Data.Map.toAscList solVariables

solVarToLpAssignment :: Set Variable -> Var -> Scientific -> LpAssignment
solVarToLpAssignment variablesDeclared var number =
  case Data.Set.toList $ Data.Set.filter (\Variable{name} -> unpack name == fromVar var) variablesDeclared of
    [variable] ->
      LpAssignment
        { variableAssigned = variable
        , resultAssigned = case variable.lpType of
            -- FIXME should check bounds here
            LpInteger _ _ -> IntegerLiteral $ round number
            LpFloat _ _ -> FloatLiteral number
        }
    [] -> error "No such variable"
    _ -> error "Several variables"

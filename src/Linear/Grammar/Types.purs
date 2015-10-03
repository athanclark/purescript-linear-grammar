module Linear.Grammar.Types where

import Prelude

import Linear.Class

import qualified Data.String as String
import Data.Monoid
import Data.Tuple
import Data.List
import Data.Int
import Data.These
import Data.Rational hiding (toNumber)
import Data.Foldable
import Data.Traversable
import qualified Data.Map as Map
import Control.Monad
import Control.Apply

import Test.StrongCheck
import Test.StrongCheck.Gen


-- * Classes

class HasNames a where
  names :: a -> Array LinVarName
  mapNames :: (LinVarName -> LinVarName) -> a -> a

instance hasNamesMap :: (HasNames b) => HasNames (Map.Map LinVarName b) where
  names xs = fromList $ (Map.keys xs) ++ concatMap (toList <<< names) (Map.values xs)
  mapNames f xs = Map.fromList $ foldr go Nil $ Map.toList xs
    where
      go (Tuple k v) acc = Cons (Tuple (f k) $ mapNames f v) acc

instance hasNamesString :: HasNames String where
  names x = [VarMain x]
  mapNames f = unLinVarName <<< f <<< VarMain

-- | `mapNames` cannot change the name type!
instance hasNamesInt :: HasNames Int where
  names x = [VarSlack x]
  mapNames f x = unVarSlack $ f $ VarSlack x

class HasVariables (a :: * -> *) where
  vars :: forall b. a b -> LinVarMap b
  mapVars :: forall b0 b1. (LinVarMap b0 -> LinVarMap b1) -> a b0 -> a b1

class HasCoefficients (a :: * -> *) where
  coeffVals :: forall b. a b -> Array b
  mapCoeffVals :: forall b0 b1. (b0 -> b1) -> a b0 -> a b1

class HasConstant a where
  constVal :: a -> Rational
  mapConst :: (Rational -> Rational) -> a -> a

-- * User-facing API

-- | User-facing abstract syntax tree
data LinAst =
    EVar String
  | ELit Rational
  | ECoeff LinAst Rational
  | EAdd LinAst LinAst

instance showLinAst :: Show LinAst where
  show (EVar n) = "EVar " ++ n
  show (ELit r) = "ELit " ++ show r
  show (ECoeff e r) = "ECoeff (" ++ show e ++ ") " ++ show r
  show (EAdd e1 e2) = "EAdd (" ++ show e1 ++ ") (" ++ show e2 ++ ")"

instance eqLinAst :: Eq LinAst where
  eq (EVar x) (EVar y) = x == y
  eq (ELit x) (ELit y) = x == y
  eq (ECoeff e1 x) (ECoeff e2 y) = e1 == e2 && x == y
  eq (EAdd x1 x2) (EAdd y1 y2) = x1 == y1 && x2 == y2

instance hasNamesLinAst :: HasNames LinAst where
  names (EVar n)     = [VarMain n]
  names (ELit _)     = []
  names (ECoeff e _) = names e
  names (EAdd e1 e2) = names e1 ++ names e2
  mapNames f (EVar n)     = EVar <<< unLinVarName <<< f <<< VarMain $ n
  mapNames _ (ELit x)     = ELit x
  mapNames f (ECoeff e c) = ECoeff (mapNames f e) c
  mapNames f (EAdd e1 e2) = EAdd (mapNames f e1) (mapNames f e2)

instance arbitraryLinAst :: Arbitrary LinAst where
  arbitrary = sized go
    where
      go :: Int -> Gen LinAst
      go s | s <= 1 = oneOf (EVar <$> stringName)
                            [ ELit <$> between1000Rational
                            ]
           | otherwise = oneOf (EVar <$> stringName)
                               [ ELit <$> between1000Rational
                               , lift2 ECoeff (resize (s-1) arbitrary)
                                              between1000Rational
                               , do n <- chooseInt (toNumber 0) (toNumber $ s-1)
                                    lift2 EAdd (resize n arbitrary)
                                               (resize n arbitrary)
                               ]


instance canMultiplyToLinAstLinAstLinAst :: CanAddTo LinAst LinAst LinAst where
  (.+.) = EAdd

instance canMultiplyToLinAstRationalLinAst :: CanMultiplyTo LinAst Rational LinAst where
  (.*.) = ECoeff

instance canMultiplyToRationalLinAstLinAst :: CanMultiplyTo Rational LinAst LinAst where
  (.*.) = flip ECoeff


-- * Variables

data ErrorSign = ErrNeg | ErrPos

instance showErrorSign :: Show ErrorSign where
  show ErrNeg = "ErrNeg"
  show ErrPos = "ErrPos"

instance eqErrorSign :: Eq ErrorSign where
  eq ErrNeg ErrNeg = true
  eq ErrPos ErrPos = true
  eq _ _ = false

instance ordErrorSign :: Ord ErrorSign where
  compare ErrNeg ErrPos = LT
  compare ErrPos ErrNeg = GT
  compare ErrNeg ErrNeg = EQ
  compare ErrPos ErrPos = EQ

instance arbitraryErrorSign :: Arbitrary ErrorSign where
  arbitrary = boolToErrorSign <$> arbitrary

isErrPos :: ErrorSign -> Boolean
isErrPos ErrPos = true
isErrPos _      = false

isErrNeg :: ErrorSign -> Boolean
isErrNeg = not <<< isErrPos

boolToErrorSign :: Boolean -> ErrorSign
boolToErrorSign b = if b then ErrPos else ErrNeg

data LinVarName =
    VarMain  String
  | VarSlack Int
  | VarError String ErrorSign

instance showLinVarName :: Show LinVarName where
  show (VarMain s) = "VarMain " ++ s
  show (VarSlack i) = "VarSlack " ++ show i
  show (VarError s e) = "VarError " ++ s ++ " " ++ show e

instance eqLinVarName :: Eq LinVarName where
  eq (VarMain x) (VarMain y) = x == y
  eq (VarSlack x) (VarSlack y) = x == y
  eq (VarError x e1) (VarError y e2) = x == y && e1 == e2

instance ordLinVarName :: Ord LinVarName where
  compare (VarMain _) (VarSlack _) = GT
  compare (VarMain _) (VarError _ _) = GT
  compare (VarSlack _) (VarError _ _) = GT
  compare (VarError _ _) (VarMain _) = LT
  compare (VarError _ _) (VarSlack _) = LT
  compare (VarSlack _) (VarMain _) = LT
  compare (VarMain x) (VarMain y) = compare x y
  compare (VarSlack x) (VarSlack y) = compare x y
  compare (VarError x e1) (VarError y e2) = compare x y <> compare e1 e2

unVarSlack :: LinVarName -> Int
unVarSlack (VarSlack i) = i

instance hasNamesLinVarName :: HasNames LinVarName where
  names n = [n]
  mapNames = ($)

unLinVarName :: LinVarName -> String
unLinVarName (VarMain n)    = n
unLinVarName (VarSlack n)   = show n
unLinVarName (VarError n b) = "error_" ++ n ++ if isErrPos b then "_+"
                                                             else "_-"

mapLinVarName :: (String -> String) -> LinVarName -> LinVarName
mapLinVarName f (VarMain n)    = VarMain $ f n
mapLinVarName f (VarError n b) = VarError (f n) b
mapLinVarName _ n              = n

instance arbitraryLinVarName :: Arbitrary LinVarName where
  arbitrary = oneOf (VarMain  <$> stringName)
                    [ VarSlack <$> arbitrary `suchThat` (\x -> x <= 1000 && x >= 0)
                    , lift2 VarError stringName arbitrary
                    ]


data LinVar = LinVar LinVarName Rational

instance showLinVar :: Show LinVar where
  show (LinVar n c) = "LinVarName (" ++ show n ++ ") " ++ show c

instance eqLinVar :: Eq LinVar where
  eq (LinVar x c1) (LinVar y c2) = x == y && c1 == c2

-- | Name-based ordering
instance ordLinVar :: Ord LinVar where
  compare (LinVar x _) (LinVar y _) = compare x y

instance hasNamesLinVar :: HasNames LinVar where
  names (LinVar n _) = [n]
  mapNames f (LinVar n c) = LinVar (f n) c

instance arbitraryLinVar :: Arbitrary LinVar where
  arbitrary = lift2 LinVar arbitrary between1000Rational


linVarHasName :: String -> LinVar -> Boolean
linVarHasName n (LinVar m _) = n == unLinVarName m

linVarHasCoeff :: Rational -> LinVar -> Boolean
linVarHasCoeff x (LinVar _ y) = x == y

-- * Variables with Coefficients

-- | Mapping from variable names, to a polymorphic coefficient type.
newtype LinVarMap b = LinVarMap (Map.Map LinVarName b)

instance showLinVarMap :: (Show b) => Show (LinVarMap b) where
  show (LinVarMap xs) = show xs

instance eqLinVarMap :: (Eq b) => Eq (LinVarMap b) where
  eq (LinVarMap xs) (LinVarMap ys) = xs == ys

instance functorLinVarMap :: Functor LinVarMap where
  map f (LinVarMap xs) = LinVarMap $ map f xs

instance foldableLinVarMap :: Foldable LinVarMap where
  foldr f a (LinVarMap xs) = foldr f a xs
  foldl f a (LinVarMap xs) = foldl f a xs
  foldMap f (LinVarMap xs) = foldMap f xs

instance traversableLinVarMap :: Traversable LinVarMap where
  sequence (LinVarMap xs) = LinVarMap <$> sequence xs
  traverse f (LinVarMap xs) = LinVarMap <$> traverse f xs

instance semigroupLinVarMap :: Semigroup (LinVarMap b) where
  append (LinVarMap xs) (LinVarMap ys) = LinVarMap (xs <> ys)

instance monoidLinVarMap :: Monoid (LinVarMap b) where
  mempty = LinVarMap mempty

linVarMapCoeffVals :: forall b. LinVarMap b -> List b
linVarMapCoeffVals (LinVarMap m) = Map.values m

linVarMapMapCoeffs :: forall b0 b1. (b0 -> b1) -> LinVarMap b0 -> LinVarMap b1
linVarMapMapCoeffs f (LinVarMap m) = LinVarMap $ f <$> m

instance canAddToLinVarMapLinVarMapLinVarMap :: CanAddTo (LinVarMap Rational) (LinVarMap Rational) (LinVarMap Rational) where
  (.+.) (LinVarMap x) (LinVarMap y) =
    let x' = This <$> x
        y' = That <$> y
        xs :: Map.Map LinVarName (These b b)
        xs = Map.unionWith (\(This a) (That b) -> Both a b) x' y'
        ys :: List (Tuple LinVarName b)
        ys = foldr go Nil (Map.toList xs)
    in LinVarMap (Map.fromList ys)
    where
      go (Tuple k (Both v1 v2)) acc | (v1 + v2) == 0 % 1 = acc
                                    | otherwise          = Cons (Tuple k (v1+v2)) acc

instance canSubToLinVarMapLinVarMapLinVarMap :: CanSubTo (LinVarMap Rational) (LinVarMap Rational) (LinVarMap Rational) where
  (.-.) (LinVarMap x) (LinVarMap y) =
    let x' = This <$> x
        y' = That <$> y
        xs :: Map.Map LinVarName (These b b)
        xs = Map.unionWith (\(This a) (That b) -> Both a b) x' y'
        ys :: List (Tuple LinVarName b)
        ys = foldr go Nil (Map.toList xs)
    in LinVarMap (Map.fromList ys)
    where
      go (Tuple k (Both v1 v2)) acc | (v1 - v2) == 0 % 1 = acc
                                    | otherwise          = Cons (Tuple k (v1-v2)) acc


instance hasNamesLinVarMap :: HasNames (LinVarMap b) where
  names (LinVarMap x) = fromList $ Map.keys x
  mapNames f (LinVarMap x) = LinVarMap $ Map.fromList $ foldr go Nil $ Map.toList x
    where
      go (Tuple k v) acc = Cons (Tuple (f k) v) acc

instance hasVariablesLinVarMap :: HasVariables LinVarMap where
  vars = id
  mapVars = ($)

instance hasCoefficientsLinVarMap :: HasCoefficients LinVarMap where
  coeffVals    = fromList <<< linVarMapCoeffVals
  mapCoeffVals = linVarMapMapCoeffs

arbitraryMap :: forall k v. (Arbitrary k, Arbitrary v, Ord k) => Gen (Map.Map k v)
arbitraryMap = sized go
  where
    go s = do
      n <- chooseInt (toNumber 0) (toNumber s)
      xs <- replicateM n (Tuple <$> arbitrary <*> arbitrary)
      return (Map.fromList xs)

instance arbitraryLinVarMap :: (IsZero b, Arbitrary b) => Arbitrary (LinVarMap b) where
  arbitrary = do
    LinVarMap <$> arbitraryMap `suchThat`
      (\x -> Map.size x <= 100 && Map.size x > 0 && not (any isZero' x))


-- * Expressions

-- | Linear expressions suited for normal and standard form.
data LinExpr = LinExpr (LinVarMap Rational) Rational

instance showLinExpr :: Show LinExpr where
  show (LinExpr xs xc) = "LinExpr (" ++ show xs ++ ") " ++ show xc

instance eqLinExpr :: Eq LinExpr where
  eq (LinExpr xs xc) (LinExpr ys yc) = xs == ys && xc == yc

instance hasNamesLinExpr :: HasNames LinExpr where
  names (LinExpr xs _) = names xs
  mapNames f (LinExpr xs xc) = LinExpr (mapNames f xs) xc

instance hasConstant :: HasConstant LinExpr where
  constVal (LinExpr _ xc) = xc
  mapConst f (LinExpr xs xc) = LinExpr xs $ f xc

instance arbitraryLinExpr :: Arbitrary LinExpr where
  arbitrary = sized $ \s -> do
    xc <- between1000Rational
    n  <- chooseInt (toNumber 0) (toNumber s)
    xs <- Map.fromList <$> replicateM n (Tuple <$> arbitrary <*> between1000Rational)
    return (LinExpr (LinVarMap xs) xc)

mergeLinExpr :: LinExpr -> LinExpr -> LinExpr
mergeLinExpr (LinExpr (LinVarMap vs1) x) (LinExpr (LinVarMap vs2) y) =
  LinExpr (LinVarMap (vs1 `Map.union` vs2)) (x + y)

instance semigroupLinExpr :: Semigroup LinExpr where
  append = mergeLinExpr

instance monoidLinExpr :: Monoid LinExpr where
  mempty = LinExpr mempty (0 % 1)


-- * Equations

-- | User-level inequalities
data IneqExpr =
    EquExpr LinExpr LinExpr
  | LteExpr LinExpr LinExpr

instance showIneqExpr :: Show IneqExpr where
  show (EquExpr e1 e2) = "EquExpr (" ++ show e1 ++ ") (" ++ show e2 ++ ")"
  show (LteExpr e1 e2) = "LteExpr (" ++ show e1 ++ ") (" ++ show e2 ++ ")"

instance eqIneqExpr :: Eq IneqExpr where
  eq (EquExpr x1 x2) (EquExpr y1 y2) = eq x1 y1 && eq x2 y2
  eq (LteExpr x1 x2) (LteExpr y1 y2) = eq x1 y1 && eq x2 y2
  eq _ _ = false

instance hasNamesIneqExpr :: HasNames IneqExpr where
  names (EquExpr x y) = names x ++ names y
  names (LteExpr x y) = names x ++ names y
  mapNames f (EquExpr x y) = EquExpr (mapNames f x) (mapNames f y)
  mapNames f (LteExpr x y) = LteExpr (mapNames f x) (mapNames f y)

instance arbitraryIneqExpr :: Arbitrary IneqExpr where
  arbitrary = oneOf
    (lift2 EquExpr arbitrary arbitrary)
    [ lift2 LteExpr arbitrary arbitrary
    ]

-- * Standard Form Equations

-- Exact equality
data Equality b = Equ (LinVarMap b) Rational

instance showEquality :: (Show b) => Show (Equality b) where
  show (Equ xs xc) = "Equ (" ++ show xs ++ ") " ++ show xc

instance eqEquality :: (Eq b) => Eq (Equality b) where
  eq (Equ xs xc) (Equ ys yc) = eq xs ys && eq xc yc

instance functorEquality :: Functor Equality where
  map f (Equ xs xc) = Equ (map f xs) xc

instance foldableEquality :: Foldable Equality where
  foldr f a (Equ xs _) = foldr f a xs
  foldl f a (Equ xs _) = foldl f a xs
  foldMap f (Equ xs _) = foldMap f xs

instance traversableEquality :: Traversable Equality where
  sequence (Equ xs xc) = (flip Equ xc) <$> sequence xs
  traverse f (Equ xs xc) = (flip Equ xc) <$> traverse f xs

instance hasNamesEquality :: HasNames (Equality b) where
  names (Equ xs _) = names xs
  mapNames f (Equ xs xc) = Equ (mapNames f xs) xc

instance hasVariablesEquality :: HasVariables Equality where
  vars (Equ xs _) = xs
  mapVars f (Equ xs xc) = Equ (mapVars f xs) xc

instance hasCoefficientsEquality :: HasCoefficients Equality where
  coeffVals (Equ xs _) = coeffVals xs
  mapCoeffVals f (Equ xs xc) = Equ (mapCoeffVals f xs) xc

instance hasConstantEquality :: HasConstant (Equality b) where
  constVal (Equ _ xc) = xc
  mapConst f (Equ xs xc) = Equ xs $ f xc

instance arbitraryEquality :: (IsZero b, Arbitrary b) => Arbitrary (Equality b) where
  arbitrary = lift2 Equ arbitrary between1000Rational

-- Less-than inequality
data LInequality b = Lte (LinVarMap b) Rational

instance showLInequality :: (Show b) => Show (LInequality b) where
  show (Lte xs xc) = "Lte (" ++ show xs ++ ") " ++ show xc

instance eqLInequality :: (Eq b) => Eq (LInequality b) where
  eq (Lte xs xc) (Lte ys yc) = eq xs ys && eq xc yc

instance functorLInequality :: Functor LInequality where
  map f (Lte xs xc) = Lte (map f xs) xc

instance foldableLInequality :: Foldable LInequality where
  foldr f a (Lte xs _) = foldr f a xs
  foldl f a (Lte xs _) = foldl f a xs
  foldMap f (Lte xs _) = foldMap f xs

instance traversableLInequality :: Traversable LInequality where
  sequence (Lte xs xc) = (flip Lte xc) <$> sequence xs
  traverse f (Lte xs xc) = (flip Lte xc) <$> traverse f xs

instance hasNamesLInequality :: HasNames (LInequality b) where
  names (Lte xs _) = names xs
  mapNames f (Lte xs xc) = Lte (mapNames f xs) xc

instance hasVariablesLInequality :: HasVariables LInequality where
  vars (Lte xs _) = xs
  mapVars f (Lte xs xc) = Lte (mapVars f xs) xc

instance hasCoefficientsLInequality :: HasCoefficients LInequality where
  coeffVals (Lte xs _) = coeffVals xs
  mapCoeffVals f (Lte xs xc) = Lte (mapCoeffVals f xs) xc

instance hasConstantLInequality :: HasConstant (LInequality b) where
  constVal (Lte _ xc) = xc
  mapConst f (Lte xs xc) = Lte xs $ f xc

instance arbitraryLInequality :: (IsZero b, Arbitrary b) => Arbitrary (LInequality b) where
  arbitrary = lift2 Lte arbitrary between1000Rational

-- Greater-than inequality
data GInequality b = Gte (LinVarMap b) Rational

instance showGInequality :: (Show b) => Show (GInequality b) where
  show (Gte xs xc) = "Gte (" ++ show xs ++ ") " ++ show xc

instance eqGInequality :: (Eq b) => Eq (GInequality b) where
  eq (Gte xs xc) (Gte ys yc) = eq xs ys && eq xc yc

instance functorGInequality :: Functor GInequality where
  map f (Gte xs xc) = Gte (map f xs) xc

instance foldableGInequality :: Foldable GInequality where
  foldr f a (Gte xs _) = foldr f a xs
  foldl f a (Gte xs _) = foldl f a xs
  foldMap f (Gte xs _) = foldMap f xs

instance traversableGInequality :: Traversable GInequality where
  sequence (Gte xs xc) = (flip Gte xc) <$> sequence xs
  traverse f (Gte xs xc) = (flip Gte xc) <$> traverse f xs

instance hasNamesGInequality :: HasNames (GInequality b) where
  names (Gte xs _) = names xs
  mapNames f (Gte xs xc) = Gte (mapNames f xs) xc

instance hasVariablesGInequality :: HasVariables GInequality where
  vars (Gte xs _) = xs
  mapVars f (Gte xs xc) = Gte (mapVars f xs) xc

instance hasCoefficientsGInequality :: HasCoefficients GInequality where
  coeffVals (Gte xs _) = coeffVals xs
  mapCoeffVals f (Gte xs xc) = Gte (mapCoeffVals f xs) xc

instance hasConstantGInequality :: HasConstant (GInequality b) where
  constVal (Gte _ xc) = xc
  mapConst f (Gte xs xc) = Gte xs $ f xc

instance arbitraryGInequality :: (IsZero b, Arbitrary b) => Arbitrary (GInequality b) where
  arbitrary = lift2 Gte arbitrary between1000Rational

-- | Internal structure for linear equations
data IneqStdForm b =
    EquStd (Equality b)
  | LteStd (LInequality b)
  | GteStd (GInequality b)

instance showIneqStdForm :: (Show b) => Show (IneqStdForm b) where
  show (EquStd xs) = "EquStd (" ++ show xs ++ ")"
  show (LteStd xs) = "LteStd (" ++ show xs ++ ")"
  show (GteStd xs) = "GteStd (" ++ show xs ++ ")"

instance eqIneqStdForm :: (Eq b) => Eq (IneqStdForm b) where
  eq (EquStd xs) (EquStd ys) = eq xs ys
  eq (LteStd xs) (LteStd ys) = eq xs ys
  eq (GteStd xs) (GteStd ys) = eq xs ys
  eq _ _ = false

instance functorIneqStdForm :: Functor IneqStdForm where
  map f (EquStd xs) = EquStd (map f xs)
  map f (LteStd xs) = LteStd (map f xs)
  map f (GteStd xs) = GteStd (map f xs)

instance foldableIneqStdForm :: Foldable IneqStdForm where
  foldr f a (EquStd xs) = foldr f a xs
  foldr f a (LteStd xs) = foldr f a xs
  foldr f a (GteStd xs) = foldr f a xs

  foldl f a (EquStd xs) = foldl f a xs
  foldl f a (LteStd xs) = foldl f a xs
  foldl f a (GteStd xs) = foldl f a xs

  foldMap f (EquStd xs) = foldMap f xs
  foldMap f (LteStd xs) = foldMap f xs
  foldMap f (GteStd xs) = foldMap f xs

instance traversableIneqStdForm :: Traversable IneqStdForm where
  sequence (EquStd xs) = EquStd <$> sequence xs
  sequence (LteStd xs) = LteStd <$> sequence xs
  sequence (GteStd xs) = GteStd <$> sequence xs

  traverse f (EquStd xs) = EquStd <$> traverse f xs
  traverse f (LteStd xs) = LteStd <$> traverse f xs
  traverse f (GteStd xs) = GteStd <$> traverse f xs

instance hasNamesIneqStdForm :: HasNames (IneqStdForm b) where
  names (EquStd x) = names x
  names (LteStd x) = names x
  names (GteStd x) = names x
  mapNames f (EquStd x) = EquStd $ mapNames f x
  mapNames f (LteStd x) = LteStd $ mapNames f x
  mapNames f (GteStd x) = GteStd $ mapNames f x

instance hasVariablesIneqStdForm :: HasVariables IneqStdForm where
  vars (EquStd x) = vars x
  vars (LteStd x) = vars x
  vars (GteStd x) = vars x
  mapVars f (EquStd x) = EquStd $ mapVars f x
  mapVars f (LteStd x) = LteStd $ mapVars f x
  mapVars f (GteStd x) = GteStd $ mapVars f x

instance hasCoefficientsIneqStdForm :: HasCoefficients IneqStdForm where
  coeffVals (EquStd x) = coeffVals x
  coeffVals (LteStd x) = coeffVals x
  coeffVals (GteStd x) = coeffVals x
  mapCoeffVals f (EquStd x) = EquStd $ mapCoeffVals f x
  mapCoeffVals f (LteStd x) = LteStd $ mapCoeffVals f x
  mapCoeffVals f (GteStd x) = GteStd $ mapCoeffVals f x

instance hasConstantIneqStdForm :: HasConstant (IneqStdForm b) where
  constVal (EquStd x) = constVal x
  constVal (LteStd x) = constVal x
  constVal (GteStd x) = constVal x
  mapConst f (EquStd x) = EquStd $ mapConst f x
  mapConst f (LteStd x) = LteStd $ mapConst f x
  mapConst f (GteStd x) = GteStd $ mapConst f x

instance arbitraryIneqStdForm :: (IsZero b, Arbitrary b) => Arbitrary (IneqStdForm b) where
  arbitrary = oneOf
    (EquStd <$> arbitrary)
    [ LteStd <$> arbitrary
    , GteStd <$> arbitrary
    ]



-- * Orphan instances

between1000Rational :: Gen Rational
between1000Rational = fromInt <$> (chooseInt (toNumber 0) (toNumber 1000))


stringName :: Gen String
stringName = arbitrary `suchThat`
  (\x -> String.length x < 5)

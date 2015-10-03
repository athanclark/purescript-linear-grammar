module Linear.Class where

import Prelude

import Data.Rational


-- * Heterogeneous Arithmetic

class CanAddTo a b r where
  (.+.) :: a -> b -> r

infixr 8 .+.

instance canAddToRationalRationalRational :: CanAddTo Rational Rational Rational where
  (.+.) = (+)


class HasZero a where
  zero' :: a

instance hasZeroRational :: HasZero Rational where
  zero' = 0 % 1

class IsZero a where
  isZero' :: a -> Boolean

instance isZeroRational :: IsZero Rational where
  isZero' x = x == (0 % 1)

class HasOne a where
  one' :: a

instance hasOneRational :: HasOne Rational where
  one' = 1 % 1

class HasNegOne a where
  negone' :: a

instance hasNegOneRational :: HasNegOne Rational where
  negone' = -1 % 1


class HasNegate a where
  negate' :: a -> a

instance hasNegateRational :: HasNegate Rational where
  negate' = negate


class CanSubTo a b r where
  (.-.) :: a -> b -> r

infixl 8 .-.

instance canSubToRationalRationalRational :: CanSubTo Rational Rational Rational where
  (.-.) = (-)


class CanMultiplyTo a b r where
  (.*.) :: a -> b -> r

infixr 9 .*.

instance canMultiplyToRationalRationalRational :: CanMultiplyTo Rational Rational Rational where
  (.*.) = (*)


class CanDivideTo a b r where
  (./.) :: a -> b -> r

infixl 9 ./.

instance canDivideToRationalRationalRational :: CanDivideTo Rational Rational Rational where
  (./.) = (/)

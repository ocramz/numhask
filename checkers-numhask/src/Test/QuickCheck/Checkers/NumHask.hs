module Test.QuickCheck.Checkers.NumHask where

import Control.Applicative (liftA2, liftA3)

import Test.QuickCheck (Property, Arbitrary, arbitrary, Gen, Testable(..), property, forAll, (.&.), (==>), (===), conjoin, sized, resize) 
import Test.QuickCheck.Checkers
import Test.QuickCheck.Utils

import Prelude hiding (Num(..))
import NumHask.Algebra



-- | Unital Magma
unital :: (Show a, Eq a, Unital a) => Gen a -> Property
unital gen =
    forAll gen $ \a -> conjoin [
        a ⊕ unit `eq` a
      , unit ⊕ a `eq` a
      ]





-- * Combinators

-- | Additive unital
nonZero :: (Eq a, AdditiveUnital a) => Gen a -> Gen a
nonZero g =
  sized (\s -> satisfiesM (/= zero) (if s == zero then resize one g else g))


-- | Signed
nonNegative :: (Signed a, Arbitrary a) => Gen a
nonNegative = abs <$> arbitrary

positive :: (Eq a, Arbitrary a, AdditiveUnital a, Signed a) => Gen a
positive = nonZero nonNegative

nonPositive :: (Signed a, AdditiveInvertible a, Arbitrary a) => Gen a
nonPositive = negate <$> nonNegative








-- * Control combinators

satisfiesM :: Monad m => (a -> Bool) -> m a -> m a
satisfiesM p x = x >>= if' p return (const (satisfiesM p x))

if' :: Applicative f => f Bool -> f a -> f a -> f a
if' = liftA3 (\ c t e -> if c then t else e)





-- * PLAYGROUND

-- -- funEq :: (Arbitrary t, Show t, Eq a) => (t -> a) -> (t -> a) -> Property
-- -- funEq f g = property $ \x -> f x == g x

-- funEq :: (Show t, Eq a) => Gen t -> (t -> a) -> (t -> a) -> Property
-- funEq gen f g = 
--   forAll gen $ \x ->
--     f x `eq` g x

-- associative gen =
--   property $ \a ->
--     forAll (gen a)

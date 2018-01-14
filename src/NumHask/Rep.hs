{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}

-- | https://github.com/Icelandjack/deriving-via/blob/master/haskellx-presentation/Presentation.md
module NumHask.Rep where

import DerivingVia

import Protolude hiding (Rep)
import Data.Functor.Rep
import Data.Distributive
import Data.Functor.Adjunction
import Data.Kind (Type)
import qualified Data.Vector as V
-- import Data.Coerce

newtype WrappedRep f a = Rep_ (f a)
  deriving (Functor, Show)
  deriving newtype Representable

instance Representable r => Distributive (WrappedRep r) where
  distribute :: Functor f => f (WrappedRep r a) -> WrappedRep r (f a)
  distribute = distributeRep

instance (Representable f) => Applicative (WrappedRep f) where
  pure = pureRep
  (<*>) = apRep

newtype Vec (n :: Nat) a = Vec (V.Vector a)
  deriving (Eq, Functor, Foldable)

-- deriveVia ''Applicative ''Vec ''WrappedRep
-- $(stringE . show =<< dsReify ''Vec)

instance forall n. (KnownNat n) => Distributive (Vec n) where
  distribute f =
    Vec $ V.generate n $ \i -> fmap (\(Vec v) -> V.unsafeIndex v i) f
    where
      n = fromInteger $ natVal (Proxy :: Proxy n)

instance forall n. (KnownNat n) => Representable (Vec n) where
  type Rep (Vec n) = Int
  tabulate = Vec . V.generate n
    where
      n = fromInteger $ natVal (Proxy :: Proxy n)
  index (Vec xs) i = xs V.! i


-- from https://gist.github.com/Icelandjack/dab7111ba9ee2d1e25cf8728f7864e06
newtype App f a = App_ (f a)
  deriving (Functor, Show)
  deriving newtype Applicative

instance (Applicative f, Num a) => Num (App f a) where
  (+)         = liftA2 (+)
  (*)         = liftA2 (*)
  negate      = fmap negate
  fromInteger = pure . fromInteger
  abs         = fmap abs
  signum      = fmap signum

instance (Applicative f, Fractional a) => Fractional (App f a) where
  recip        = fmap recip
  fromRational = pure . fromRational

instance (Applicative f, Floating a) => Floating (App f a) where
  pi    = pure pi
  sqrt  = fmap sqrt
  exp   = fmap exp
  log   = fmap log
  sin   = fmap sin
  cos   = fmap cos
  asin  = fmap asin
  atan  = fmap atan
  acos  = fmap acos
  sinh  = fmap sinh
  cosh  = fmap cosh
  asinh = fmap asinh
  atanh = fmap atanh
  acosh = fmap acosh

-- from https://www.reddit.com/r/haskell/comments/6ox9ev/adjunctions_and_battleship/
newtype WrappedAdj :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) where
  WrapAdj :: u a -> WrappedAdj f u a
  deriving Functor

instance Adjunction f u => Distributive (WrappedAdj f u) where
  distribute :: Functor g => g (WrappedAdj f u a) -> WrappedAdj f u (g a)
  distribute = distributeRep

instance Adjunction f u => Representable (WrappedAdj f u) where
  type Rep (WrappedAdj f u) = f ()

  index :: WrappedAdj f u a -> (f () -> a)
  index (WrapAdj ua) = indexAdjunction ua

  tabulate :: (f () -> a) -> WrappedAdj f u a
  tabulate f = WrapAdj (tabulateAdjunction f)

data (:!) r b = b :! Rep r deriving (Functor)

newtype Arr r b = Arr (r b) deriving newtype (Functor, Representable)

instance Representable r => Distributive (Arr r) where
  distribute :: Functor f => f (Arr r a) -> Arr r (f a)
  distribute = distributeRep

instance Representable r => Adjunction ((:!) r) (Arr r) where
  unit :: a -> Arr r (r :! a)
  unit = Arr . tabulate . (:!)

  counit :: r :! Arr r a -> a
  counit (xs :! rep) = xs `index` rep

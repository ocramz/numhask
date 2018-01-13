{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}

-- | https://github.com/Icelandjack/deriving-via/blob/master/haskellx-presentation/Presentation.md
-- https://gist.github.com/Icelandjack/1f578e7103ff327cbcfb3426c005e26c#gistcomment-2134119
module NumHask.Rep where

import Protolude hiding (Rep)
import Data.Semigroup
import Control.Applicative
import TH
import Data.Functor.Rep
import Data.Distributive

data Opt a = None | Some a
deriveVia ''Functor     ''Opt ''WrappedMonad
deriveVia ''Applicative ''Opt ''WrappedMonad

instance Monad Opt where
  return = Some

  None   >>= _ = None
  Some a >>= k = k a

data U = U

instance Monoid U where
  mempty = U
  mappend U U = U
deriveVia ''Semigroup ''U ''WrappedMonoid

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

newtype WrappedRep f a = Rep_ (f a)
  deriving (Functor, Show)
  -- deriving newtype Distributive
  -- deriving newtype Representable

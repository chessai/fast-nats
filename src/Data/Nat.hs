{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall -Werror #-}
module Data.Nat (
  Nat,
  natToInt,
  type FromKnownNat,
  fromKnownNat,
  zero,
  succ,
  isZero,
  notZero,
  type (+),
  plus,
  type Pred,
  pred,
  type (-),
  monus,
  type (*),
  times,
  type (^),
  power,
  type Min,
  minimum,
  type Max,
  maximum,
  type Cmp,
  Compare(..),
  cmp )where

import Prelude hiding (minimum,maximum,succ,pred)
import qualified GHC.TypeLits as GHC
import Data.Kind hiding (type (*))
import Data.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

import Data.Nat.Internal

type family FromKnownNat (a :: GHC.Nat) :: Nat where
  FromKnownNat 0 = 'Z
  FromKnownNat n = 'S (FromKnownNat (n GHC.- 1))

fromKnownNat :: forall proxy n. (GHC.KnownNat n) => proxy n -> SNat (FromKnownNat n)
fromKnownNat _ = (SNat . fromIntegral . GHC.natVal) (Proxy :: Proxy n)

zero :: SNat 'Z
zero = SNat 0

succ :: SNat n -> SNat ('S n)
succ (SNat x) = SNat (1 + x)

isZero :: SNat n -> Bool
isZero (SNat n) = n == 0

notZero :: SNat n -> Bool
notZero (SNat n) = n /= 0

type family (a :: Nat) + (b :: Nat) :: Nat where
  'Z + n = n
  ('S n) + m = 'S (n + m)

plus :: SNat a -> SNat b -> SNat (a + b)
plus (SNat x) (SNat y) = SNat (x + y)

type family Pred (a :: Nat) :: Nat where
  Pred 'Z = 'Z
  Pred ('S n) = n

pred :: SNat n -> SNat (Pred n)
pred (SNat 0) = SNat 0
pred (SNat n) = SNat (n - 1)

type family (a :: Nat) - (b :: Nat) :: Nat where
  n - 'Z = n
  'Z - m = m
  'S n - 'S m = n - m

monus :: SNat a -> SNat b -> SNat (a - b)
monus (SNat x) (SNat y)
  | x >= y    = SNat (x - y)
  | otherwise = SNat 0

type family (a :: Nat) * (b :: Nat) :: Nat where
  'Z * n = 'Z
  ('S n) * m = m + (n * m)

times :: SNat a -> SNat b -> SNat (a * b)
times (SNat x) (SNat y) = SNat (x * y)

type family (a :: Nat) ^ (b :: Nat) :: Nat where
  base ^ 'Z = 'S 'Z
  base ^ 'S n = base * (base ^ n)

power :: SNat a -> SNat b -> SNat (a ^ b)
power (SNat x) (SNat y) = SNat (x ^ y)

type family Min (a :: Nat) (b :: Nat) :: Nat where
  Min 'Z m = 'Z
  Min ('S 'Z) 'Z = 'Z
  Min ('S n) ('S m) = 'S (Min n m)

minimum :: SNat a -> SNat b -> SNat (Min a b)
minimum (SNat a) (SNat b) = SNat (min a b)

type family Max (a :: Nat) (b :: Nat) :: Nat where
  Max 'Z m = m
  Max ('S 'Z) 'Z = 'S 'Z
  Max ('S n) ('S m) = 'S (Max n m)

maximum :: SNat a -> SNat b -> SNat (Max a b)
maximum (SNat a) (SNat b) = SNat (max a b)

type family Cmp (a :: Nat) (b :: Nat) :: Ordering where
  Cmp 'Z 'Z = 'EQ
  Cmp ('S n) 'Z = 'GT
  Cmp 'Z ('S m) = 'LT
  Cmp ('S n) ('S m) = Cmp n m

data Compare :: Nat -> Nat -> Type where
  SLT :: SNat y -> Compare x (x + 'S y)
  SEQ :: Compare x x
  SGT :: SNat y -> Compare (x + 'S y) x

deriving instance Show (Compare n m)

cmp :: SNat a -> SNat b -> Compare a b
cmp (SNat x) (SNat y) = case compare x y of
  LT -> unsafeCoerce (SLT (SNat (y - x - 1)))
  EQ -> unsafeCoerce SEQ
  GT -> unsafeCoerce (SGT (SNat (x - y - 1)))

{-|
Module      : Data.Nat
Description : Fast natural numbers
Copyright   : (c) Kyle McKean, 2016
License     : MIT
Maintainer  : mckean.kylej@gmail.com
Stability   : experimental
Portability : Portable

Fast natural numbers, you can learn more about these types from agda and idris\' standard libary.
-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall -Werror #-}
module Data.Nat (
  Dec(..),
  type Nat(..),
  SNat,
  natToInt,
  IsNat(..),
  SomeNat,
  withNat,
  fromInt,
  type ToKnownNat,
  type FromKnownNat,
  fromKnownNat,
  zero,
  succ,
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
  IsZero(..),
  isZero,
  NotZero(..),
  notZero,
  View(..),
  viewNat,
  LTE(..),
  lte,
  Compare(..),
  cmp )where

import Prelude hiding (minimum,maximum,succ,pred)
import qualified GHC.TypeLits as GHC
import Data.Kind hiding (type (*))
import Data.Void (Void)
import Unsafe.Coerce (unsafeCoerce)

import Data.Nat.Internal

data Dec a =
  Proved a |
  Refuted (a -> Void)

newtype SomeNat = SomeNat (forall r. (forall n. SNat n -> r) -> r)

withNat :: SomeNat -> (forall n. SNat n -> r) -> r
withNat (SomeNat e) cb = e cb

fromInt :: Int -> SomeNat
fromInt i = SomeNat (\e -> e (SNat i))

-- | Transform a GHC.Typelit 'GHC.Nat' into an inductive 'Nat'.
type family FromKnownNat (a :: GHC.Nat) :: Nat where
  FromKnownNat 0 = 'Z
  FromKnownNat n = 'S (FromKnownNat (n GHC.- 1))

-- | Generate a 'SNat' from a GHC.Typelit 'GHC.Nat'.
fromKnownNat :: forall proxy n. IsNat (FromKnownNat n) => proxy n -> SNat (FromKnownNat n)
fromKnownNat _ = witness

-- | The smallest 'SNat'.
zero :: SNat 'Z
zero = SNat 0

-- | Add one to an 'SNat'.
succ :: SNat n -> SNat ('S n)
succ (SNat x) = SNat (1 + x)

-- | Type level addition of naturals.
type family (a :: Nat) + (b :: Nat) :: Nat where
  'Z + n = n
  ('S n) + m = 'S (n + m)

plus :: SNat a -> SNat b -> SNat (a + b)
plus (SNat x) (SNat y) = SNat (x + y)

-- | Type level predecessor function.
type family Pred (a :: Nat) :: Nat where
  Pred 'Z = 'Z
  Pred ('S n) = n

-- | Predecessor function, it does nothing with the natural is zero.
pred :: SNat n -> SNat (Pred n)
pred (SNat 0) = SNat 0
pred (SNat n) = SNat (n - 1)

-- | Type level monus. This is not subtraction as natural numbers do not form a group.
type family (a :: Nat) - (b :: Nat) :: Nat where
  n - 'Z = n
  'Z - m = m
  'S n - 'S m = n - m

-- | This function returns zero if the result would normally be negative.
monus :: SNat a -> SNat b -> SNat (a - b)
monus (SNat x) (SNat y)
  | x >= y    = SNat (x - y)
  | otherwise = SNat 0

-- | Type level multiplication.
type family (a :: Nat) * (b :: Nat) :: Nat where
  'Z * n = 'Z
  ('S n) * m = m + (n * m)

times :: SNat a -> SNat b -> SNat (a * b)
times (SNat x) (SNat y) = SNat (x * y)

-- | Type level exponentiation.
type family (a :: Nat) ^ (b :: Nat) :: Nat where
  base ^ 'Z = 'S 'Z
  base ^ 'S n = base * (base ^ n)

power :: SNat a -> SNat b -> SNat (a ^ b)
power (SNat x) (SNat y) = SNat (x ^ y)

-- | Type level minimum.
type family Min (a :: Nat) (b :: Nat) :: Nat where
  Min 'Z m = 'Z
  Min ('S 'Z) 'Z = 'Z
  Min ('S n) ('S m) = 'S (Min n m)

minimum :: SNat a -> SNat b -> SNat (Min a b)
minimum (SNat a) (SNat b) = SNat (min a b)

-- | Type level maximum.
type family Max (a :: Nat) (b :: Nat) :: Nat where
  Max 'Z m = m
  Max ('S 'Z) 'Z = 'S 'Z
  Max ('S n) ('S m) = 'S (Max n m)

maximum :: SNat a -> SNat b -> SNat (Max a b)
maximum (SNat a) (SNat b) = SNat (max a b)

-- | Type level comparsion. This function returns a promoted 'Ordering'.
--
-- This function is only useful when you know the natural numbers at compile time.
-- If you need to compare naturals at runtime use 'Compare'.
type family Cmp (a :: Nat) (b :: Nat) :: Ordering where
  Cmp 'Z 'Z = 'EQ
  Cmp ('S n) 'Z = 'GT
  Cmp 'Z ('S m) = 'LT
  Cmp ('S n) ('S m) = Cmp n m

-- | Proof that a natural number is zero.
data IsZero :: Nat -> Type where
  SIsZ :: IsZero 'Z

-- | This is a runtime function used to check if a 'Nat' is zero.
isZero :: SNat n -> Dec (IsZero n)
isZero (SNat x)
  | x == 0    = Proved (unsafeCoerce SIsZ)
  | otherwise = Refuted (\case{})

-- | Proof that a number is not zero
data NotZero :: Nat -> Type where
  SNotZ :: NotZero ('S n)

-- | This is a runtime function used to check if a 'Nat' is not zero.
notZero :: SNat n -> Dec (NotZero n)
notZero (SNat x)
  | x /= 0    = Proved (unsafeCoerce SNotZ)
  | otherwise = Refuted (\case{})

data View :: Nat -> Type where
  Zero :: View 'Z
  Succ :: SNat n -> View ('S n)

viewNat :: SNat n -> View n
viewNat (SNat 0) = unsafeCoerce Zero
viewNat (SNat n) = unsafeCoerce (SNat (n - 1))

-- | Constructive <=
-- n <= m => exists (k : Nat). n + k = m
data LTE :: Nat -> Nat -> Type where
  SLTE :: SNat y -> LTE (y + x) x

deriving instance Show (LTE n m)

-- | This function should be used at runtime to prove n <= m.
lte :: SNat n -> SNat m -> Dec (LTE n m)
lte (SNat x) (SNat y)
  | x <= y    = Proved (unsafeCoerce (SLTE (SNat (y - x))))
  | otherwise = Refuted unsafeCoerce

-- | Constructive 'compare'
-- n < m => exists (k : Nat). n + k + 1 = m
--
-- n == m => n = m
--
-- in > m => exists (k : Nat). n = m + k + 1
--
data Compare :: Nat -> Nat -> Type where
  SLT :: SNat y -> Compare x ('S y + x)
  SEQ :: Compare x x
  SGT :: SNat y -> Compare ('S y + x) x

deriving instance Show (Compare n m)

-- | This function should be used at runtime to compare two 'Nat's
cmp :: SNat a -> SNat b -> Compare a b
cmp (SNat x) (SNat y) = case compare x y of
  LT -> unsafeCoerce (SLT (SNat (y - x - 1)))
  EQ -> unsafeCoerce SEQ
  GT -> unsafeCoerce (SGT (SNat (x - y - 1)))

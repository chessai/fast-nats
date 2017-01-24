{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
-- {-# LANGUAGE TypeApplications #-}
-- {-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE TypeInType #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
module Data.Nat where

import Data.Kind (type Type)
import Data.Type.Equality (TestEquality(..),(:~:)(..),apply)
import Data.Type.Coercion (TestCoercion(..),repr)
import Unsafe.Coerce (unsafeCoerce)
import Data.Singletons (SingI(..),SomeSing(..))
-- import Data.Singletons.Decide (Decision(..))
import Data.Singletons.Prelude (SMaybe,Sing(..))

import Data.Nat.Internal

fromInt :: Int -> Maybe (SomeSing Nat)
fromInt i
  | 0 <= i    = Just (SomeSing (SNat i))
  | otherwise = Nothing

toInt :: SNat n -> Int
toInt (SNat i) = i

slit :: SingI (Lit n) => SNat (Lit n)
slit = sing

zero :: SNat Z
zero = SNat 0

succ :: SNat n -> SNat (S n)
succ (SNat n) = SNat (n + 1)

type family Pred (n :: Nat) :: Nat where
  Pred Z = Z
  Pred (S n) = n

pred :: SNat n -> SNat (Pred n)
pred (SNat 0) = SNat 0
pred (SNat n) = SNat (n - 1)

type family (n :: Nat) :^ (m :: Nat) :: Nat where
  base :^ Z = S Z
  base :^ (S n) = base * (base :^ n)

(%:^) :: SNat n -> SNat m -> SNat (n :^ m)
(SNat n) %:^ (SNat m) = SNat (n ^ m)

-- This data type exposes a safe induction interface for 'SNat'.
data View :: Nat -> Type where
  Zero :: View Z
  Succ :: SNat n -> View (S n)

deriving instance Show (View n)

instance TestEquality View where
  testEquality Zero     Zero     = Just Refl
  testEquality (Succ n) (Succ m) = fmap (apply Refl) (testEquality n m)
  testEquality _ _ = Nothing

instance TestCoercion View where
  testCoercion n m = fmap repr (testEquality n m)

view :: SNat n -> View n
view (SNat 0) = unsafeCoerce Zero
view (SNat n) = unsafeCoerce (Succ (SNat (n - 1)))

{-
-- | Constructive <=
-- n <= m ⇒ ∃ (k : Nat). n + k = m
data CLTE :: Nat -> Nat -> Type where
  CLTE :: Sing y -> CLTE (y + x) x

deriving instance Show (LTE n m)

-- | This function should be used at runtime to prove n <= m.
clte :: SNat n -> SNat m -> Decision (CLTE n m)
clte (SNat x) (SNat y)
  | x <= y    = Proved (unsafeCoerce (CLTE (SNat (y - x))))
  | otherwise = Disproved (\_ -> error "Data.Nat.lte: Integer equality failed.")

-- | Constructive 'compare'
-- n < m ⇒ ∃ (k : Nat). n + k + 1 = m
--
-- n == m ⇒ n = m
--
-- in > m ⇒ ∃ (k : Nat). n = m + k + 1
--
data CCompare :: Nat -> Nat -> Type where
  CLT :: Sing y -> CCompare x ('S y + x)
  CEQ :: CCompare x x
  CGT :: Sing y -> CCompare ('S y + x) x

deriving instance Show (CCompare n m)

-- | This function should be used at runtime to compare two 'Nat's
cmp :: SNat a -> SNat b -> CCompare a b
cmp (SNat x) (SNat y) = case compare x y of
  LT -> unsafeCoerce (CLT (SNat (y - x - 1)))
  EQ -> unsafeCoerce CEQ
  GT -> unsafeCoerce (CGT (SNat (x - y - 1)))
-}

data LTE :: Nat -> Nat -> Type where
  LTEZero :: LTE Z n
  LTESucc :: LTE n m -> LTE (S n) (S m)

type LT n m = LTE n (S m)

type family Map (f :: a -> b) (i :: Maybe a) :: Maybe b where
  Map f Nothing = Nothing
  Map f (Just x) = Just (f x)

type family Lte (n :: Nat) (m :: Nat) :: Maybe (LTE n m) where
  Lte Z m = Just LTEZero
  Lte (S n) Z = Nothing
  Lte (S n) (S m) = Map LTESucc (Lte n m)

data instance Sing (l :: LTE n m) = SLTE

type SLTE (l :: LTE n m) = Sing l

lte :: SNat n -> SNat m -> SMaybe (Lte n m)
lte (SNat n) (SNat m)
  | n <= m    = unsafeCoerce (SJust SLTE)
  | otherwise = unsafeCoerce SNothing

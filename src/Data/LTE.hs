{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeInType #-}
module Data.LTE where

import Data.Kind (type Type)
import Unsafe.Coerce (unsafeCoerce)
import Data.Singletons.Prelude (SMaybe,Sing(..))

import Data.Nat.Internal (Sing(..))
import Data.Nat (type Nat(..),type SNat)

data LTE :: Nat -> Nat -> Type where
  LTEZero :: LTE Z n
  LTESucc :: LTE n m -> LTE (S n) (S m)

type family Map (f :: a -> b) (i :: Maybe a) :: Maybe b where
  Map f Nothing = Nothing
  Map f (Just x) = Just (f x)

type family (n :: Nat) <= (m :: Nat) :: Maybe (LTE n m) where
  Z <= m = Just LTEZero
  (S n) <= Z = Nothing
  (S n) <= (S m) = Map LTESucc (n <= m)

data instance Sing (l :: LTE n m) = SLTE Int

type SLTE (l :: LTE n m) = Sing l

lte :: SNat n -> SNat m -> SMaybe (n <= m)
lte (SNat n) (SNat m)
  | n <= m    = unsafeCoerce (SJust (SLTE (n - m)))
  | otherwise = unsafeCoerce SNothing

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


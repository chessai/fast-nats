{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
module Data.Nat (
  type Nat(..),
  type SNat,
  View(..),
  type ToLit,
  type Lit,
  fromInt,
  toInt,
  slit,
  zero,
  succ,
  type Pred,
  pred,
  type (:^),
  (%:^)) where

import Prelude hiding (succ,pred)
import Data.Singletons (SingI(..),SomeSing(..))

import Data.Nat.Internal (type Nat(..),Sing(..),ToLit,Lit,type (*),View(..))

type SNat (n :: Nat) = Sing n

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

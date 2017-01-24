{-|
Module      : Data.Fin
Description : Fast finite sets
Copyright   : (c) Kyle McKean, 2016
License     : MIT
Maintainer  : mckean.kylej@gmail.com
Stability   : experimental
Portability : Portable
Fast finite sets, you can learn more about these types from agda and idris\' standard libary.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeInType #-}

{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Data.Fin where

import Unsafe.Coerce (unsafeCoerce)
import Data.Singletons.Prelude (Sing(..),SingI(..),SMaybe)

import Data.Nat
import Data.Nat.Internal

type family NatToFin (n :: Nat) (m :: Nat) :: Maybe (Fin m) where
  NatToFin Z     (S m) = Just FZ
  NatToFin (S n) (S m) = Map FS (NatToFin n m)
  NatToFin n m = Nothing

natToFin :: SNat n -> SNat m -> SMaybe (NatToFin n m)
natToFin (SNat n) (SNat m)
  | n < m     = unsafeCoerce (SJust (SFin n))
  | otherwise = unsafeCoerce SNothing

type family FromNat (n :: Nat) :: Fin (S n) where
  FromNat Z = FZ
  FromNat (S n) = FS (FromNat n)

fromNat :: SNat n -> SFin (FromNat n)
fromNat (SNat i) = SFin i

type family ToNat (i :: Fin n) :: Nat where
  ToNat FZ = Z
  ToNat (FS f) = S (ToNat f)

toNat :: SFin f -> SNat (ToNat f)
toNat (SFin i) = SNat i

type Fin' (i :: Fin n) = Fin (ToNat i)

-- This also seems to be broken
type family FromLTE (l :: LT n m) :: Fin m where
  FromLTE (LTESucc LTEZero) = FZ
  FromLTE (LTESucc (LTESucc n)) = FS (FromLTE (LTESucc n))

fromLTE :: forall n m lte. (SingI n) => SLTE (lte :: LT n m) -> SFin (FromLTE lte)
fromLTE _ = SFin (toInt (sing :: SNat n))

test = case lte (slit @3) (slit @4) of
  SJust l -> fromLTE l

-- | The smallest finite set, it only contains 0.
zero :: SFin FZ
zero = SFin 0

-- | Increase the value and bound of a finite set by one.
succ :: SFin f -> SFin (FS f)
succ (SFin i) = SFin (1 + i)

weaken :: SFin f -> SFin (FS f)
weaken (SFin i) = SFin i

type family WeakenLTE (lte :: LTE n m) (i :: Fin n) :: Fin m where
  WeakenLTE (LTESucc lte) FZ = FZ
  WeakenLTE (LTESucc lte) (FS i) = FS (WeakenLTE lte i)

weakenLTE :: SLTE lte -> SFin f -> SFin (WeakenLTE lte f)
weakenLTE _ (SFin i) = SFin i

type family WeakenN (n :: Nat) (i :: Fin m) :: (Fin (m + n)) where
  WeakenN n FZ = FZ
  WeakenN n (FS i) = FS (WeakenN n i)

weakenN :: SFin f -> SFin (WeakenN n f)
weakenN (SFin i) = SFin i

-- This seems to be broke
type family Strengthen (m :: Nat) (i :: Fin (S m)) :: Maybe (Fin m) where
  Strengthen (S k) FZ = Just FZ
  Strengthen (S k) (FS f) = Map FS (Strengthen k f)
  Strengthen k f = Nothing

strengthen :: forall n f. SingI n => SFin (f :: Fin (S n)) -> SMaybe (Strengthen n f)
strengthen (SFin i)
  | i < toInt (sing :: SNat n) = unsafeCoerce (SJust (SFin i))
  | otherwise                  = unsafeCoerce SNothing

type family Shift (n :: Nat) (i :: Fin m) :: Fin (n + m) where
  Shift Z f = f
  Shift (S n) f = FS (Shift n f)

shift :: SNat n -> SFin f -> SFin (Shift n f)
shift (SNat x) (SFin i) = SFin (x + i)

type family Last (n :: Nat) :: Fin (S n) where
  Last Z = FZ
  Last (S n) = FS (Last n)

last :: forall n. (SingI n) => SFin (Last n)
last = SFin (toInt (sing :: SNat n))

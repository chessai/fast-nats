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
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Fin (
  Fin,
  finToInt,
  natToFin,
  finToNat,
  finZAbsurd,
  finZElim,
  zero,
  succ,
  weaken,
  weakenLTE,
  weakenN,
  strengthen,
  shift,
  last) where

import Prelude hiding (succ,last)
import Data.Kind (type Type)
import Data.Void (Void,absurd)

import Data.Nat.Internal
import qualified Data.Nat as N

-- | Given a value and a bound construct a finite set.
natToFin :: SNat n -> SNat m -> Maybe (Fin m)
natToFin x bound
  | i < natToInt bound = Just (Fin i)
  | otherwise = Nothing
  where i = natToInt x

-- | Get the size of the finite set.
finToNat :: (IsNat n) => Fin n -> SNat n
finToNat _ = witness

-- | An empty finite set is uninhabited.
finZAbsurd :: Fin 'Z -> Void
finZAbsurd = finZAbsurd

-- | Construct any value from an empty finite set as it is uninhabited.
finZElim :: Fin 'Z -> a
finZElim = absurd . finZAbsurd

-- | The smallest finite set, it only contains 0.
zero :: Fin ('S n)
zero = Fin 0

-- | Increase the value and bound of a finite set by one.
succ :: Fin n -> Fin ('S n)
succ (Fin x) = Fin (1 + x)

-- | Increase the bound of a finite set by one.
weaken :: Fin n -> Fin ('S n)
weaken (Fin x) = Fin x

-- | Given a proof that n is less than or equal to m weaken a finite set of bound n to bound m.
weakenLTE :: N.LTE n m -> Fin n -> Fin m
weakenLTE _ (Fin x) = Fin x

-- | Increase the bound on a finite set by n.
weakenN :: SNat n -> Fin m -> Fin (n N.+ m)
weakenN _ (Fin x) = Fin x

-- | Attempt to lower a bound on a finite set by one.
strengthen :: forall n. (IsNat n) => Fin (S n) -> Maybe (Fin n)
strengthen (Fin x)
  | x < natToInt (witness :: SNat n) = Just (Fin x)
  | otherwise = Nothing

-- | Increase the value and bound of a finite set by N.
shift :: SNat n -> Fin m -> Fin (n N.+ m)
shift n (Fin x) = Fin (x + natToInt n)

-- | Construct the largest value possible in a finite set.
last :: forall n. (IsNat n) => Fin ('S n)
last = Fin (natToInt (witness :: SNat n))

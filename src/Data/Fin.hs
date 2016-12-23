{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Fin (Fin
                ,finToInt
                ,natToFin
                ,finToNat
                ,finZAbsurd
                ,finZElim
                ,zero
                ,succ
                ,weaken
                ,weakenN
                ,strengthen
                ,shift
                ,last) where

import Prelude hiding (succ,last)
import Data.Kind (type Type)
import Data.Void (Void,absurd)

import Data.Nat.Internal
import qualified Data.Nat as N

natToFin :: SNat n -> SNat m -> Maybe (Fin m)
natToFin x bound
  | i < natToInt bound = Just (Fin i)
  | otherwise = Nothing
  where i = natToInt x

finToNat :: (IsNat n) => Fin n -> SNat n
finToNat _ = witness

finZAbsurd :: Fin 'Z -> Void
finZAbsurd = finZAbsurd

finZElim :: Fin 'Z -> a
finZElim = absurd . finZAbsurd

zero :: Fin ('S n)
zero = Fin 0

succ :: Fin n -> Fin ('S n)
succ (Fin x) = Fin (1 + x)

weaken :: Fin n -> Fin ('S n)
weaken (Fin x) = Fin x

weakenN :: SNat n -> Fin m -> Fin (n N.+ m)
weakenN _ (Fin x) = Fin x

strengthen :: forall n. (IsNat n) => Fin (S n) -> Maybe (Fin n)
strengthen (Fin x)
  | x < natToInt (witness :: SNat n) = Just (Fin x)
  | otherwise = Nothing

shift :: SNat n -> Fin m -> Fin (n N.+ m)
shift n (Fin x) = Fin (x + natToInt n)

last :: forall n. (IsNat n) => Fin ('S n)
last = Fin (natToInt (witness :: SNat n))

{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Fin where

import Data.Kind (type Type)
import Data.Void (Void,absurd)

import Data.Nat (type Nat(..),SNat)
import qualified Data.Nat as N

newtype Fin (a :: Nat) = Fin Int

instance Show (Fin n) where
  show = show . toInt

toInt :: Fin n -> Int
toInt (Fin n) = n

natToFin :: SNat n -> SNat m -> Maybe (Fin m)
natToFin x bound
  | i < N.toInt bound = Just (Fin i)
  | otherwise = Nothing
  where i = N.toInt x

finToNat :: Fin n -> SNat n
finToNat (Fin x) = SNat x

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

strengthen :: SNat n -> Fin (S n) -> Maybe (Fin n)
strengthen bound (Fin x)
  | x <= N.toInt bound = Just (Fin x)
  | otherwise          = Nothing

shift :: SNat n -> Fin m -> Fin (n N.+ m)
shift n (Fin x) = Fin (x + N.toInt n)

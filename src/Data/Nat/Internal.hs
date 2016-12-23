{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_HADDOCK hide, not-home #-}
{-# OPTIONS_GHC -Wall -Werror #-}
module Data.Nat.Internal where

import qualified GHC.TypeLits as GHC
import Data.Proxy (Proxy(..))
import Data.Type.Equality (TestEquality(..),(:~:)(..))
import Data.Type.Coercion (TestCoercion(..),repr)
import Unsafe.Coerce (unsafeCoerce)

data Nat = Z | S Nat

newtype SNat (a :: Nat) = SNat Int

natToInt :: SNat n -> Int
natToInt (SNat n) = n

instance Show (SNat n) where
  show = show . natToInt

instance TestEquality SNat where
  testEquality (SNat n) (SNat m)
    | n == m    = Just (unsafeCoerce Refl)
    | otherwise = Nothing

instance TestCoercion SNat where
  testCoercion n m = fmap repr (testEquality n m)

class IsNat n where
  witness :: SNat n

instance IsNat 'Z where
  witness = SNat 0

type family ToKnownNat (a :: Nat) :: GHC.Nat where
  ToKnownNat 'Z = 0
  ToKnownNat ('S n) = 1 GHC.+ ToKnownNat n

instance GHC.KnownNat (ToKnownNat ('S n)) => IsNat ('S n) where
  witness = (SNat . fromIntegral . GHC.natVal) (Proxy :: Proxy (ToKnownNat ('S n)))

newtype Fin (a :: Nat) = Fin Int deriving (Eq,Ord)

finToInt :: Fin n -> Int
finToInt (Fin n) = n

instance Show (Fin n) where
  show = show . finToInt

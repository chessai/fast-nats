{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeInType #-}

{-# OPTIONS_HADDOCK hide, not-home #-}
{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
module Data.Nat.Internal where

import qualified GHC.TypeLits as GHC
import Data.Kind (type Type)
import Data.Proxy (Proxy(..))
import Data.Type.Equality (TestEquality(..),(:~:)(..))
import Data.Type.Coercion (TestCoercion(..),repr)
import Unsafe.Coerce (unsafeCoerce)

-- | Inductive natural numbers used only for type level operations.
data Nat = Z | S Nat

-- | Singleton natural numbers, unlike inductive natural numbers this data type
-- has O(1) toInt.
newtype SNat (n :: Nat) = SNat Int

-- | Transform a SNat into an 'Int'. This has a post condition that the 'Int' is not negative.
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

-- | This class is used to emulate agda and idris\' implicit parameters.
-- It also can be used to turn a 'Nat' into an 'SNat'.
class IsNat n where
  witness :: SNat n

instance IsNat 'Z where
  witness = SNat 0

-- | Transform a GHC.Typelit 'GHC.Nat' into an inductive 'Nat'.
type family ToLit (a :: Nat) :: GHC.Nat where
  ToLit 'Z = 0
  ToLit ('S n) = 1 GHC.+ ToLit n

instance GHC.KnownNat (ToLit ('S n)) => IsNat ('S n) where
  witness = (SNat . fromIntegral . GHC.natVal) (Proxy :: Proxy (ToLit ('S n)))

-- | Finite Sets, this type has an upper bound n and can only contain numbers between ∀x. 0 <= x < n
--
-- Like 'Nat' this is only used at the type level.
--
-- Fin 1 = { 0 }
--
-- Fin 2 = { 0, 1 }
--
-- Fin 3 = { 0, 1, 2 }
data Fin :: Nat -> Type where
  FZ :: Fin (S k)
  FS :: Fin k -> Fin (S k)

-- | Singleton finite sets, this uses a fast 'SNat' under the hood.
newtype SFin (f :: Fin n) = SFin Int deriving (Eq,Ord)

-- | Get the value out of a 'Fin'. This function has a postcondition that the 'Int' x is 0 <= x < n
finToInt :: SFin i -> Int
finToInt (SFin n) = n

instance Show (SFin n) where
  show = show . finToInt

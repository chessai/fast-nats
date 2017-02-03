{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeInType #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
module Data.Nat.Internal where
import Data.Word (Word)
import qualified GHC.TypeLits as GHC
import Data.Kind (type Type)
import Data.Proxy (Proxy(..))
import Data.Type.Equality (TestEquality(..),(:~:)(..))
import Data.Type.Coercion (TestCoercion(..),repr)
import Unsafe.Coerce (unsafeCoerce)
import Data.Singletons (type Sing,SingI(..),SingKind(..),SomeSing(..))
import Data.Singletons.Decide (SDecide(..),Decision(..))
import Data.Singletons.TypeLits (type Error)
import Data.Singletons.Prelude (Sing(..))
import Data.Singletons.Prelude.Num (PNum(..),SNum(..))
import Data.Singletons.Prelude.Eq (PEq(..),SEq(..))
import Data.Singletons.Prelude.Ord (POrd(..),SOrd(..))

import Data.Viewable (Viewable(..))

data Nat = Z | S Nat

newtype instance Sing (n :: Nat) = SNat Int

instance Show (Sing (n :: Nat)) where
  show (SNat n) = show n

instance SDecide Nat where
  (SNat n) %~ (SNat m)
    | n == m    = Proved (unsafeCoerce Refl)
    | otherwise = Disproved (\Refl -> error "Data.Singletons.SDecide Nat: Integer equality failed.")

instance TestCoercion (Sing :: Nat -> Type) where
  testCoercion n m = fmap repr (testEquality n m)

type family ToLit (a :: Nat) :: GHC.Nat where
  ToLit Z = 0
  ToLit (S n) = 1 GHC.+ ToLit n

type family Lit (a :: GHC.Nat) :: Nat where
  Lit 0 = Z
  Lit n = S (Lit (n GHC.- 1))

instance SingI Z where
  sing = SNat 0

instance GHC.KnownNat (ToLit (S n)) => SingI (S n) where
  sing = (SNat . fromIntegral . GHC.natVal) (Proxy @(ToLit (S n)))

instance SingKind Nat where
  type DemoteRep Nat = Word
  fromSing (SNat n) = fromIntegral n
  toSing n = SomeSing (SNat (fromIntegral n))

instance Viewable Nat where
  data View (a :: Nat) where
    Zero :: View Z
    Succ :: Sing n -> View (S n)
  view (SNat x)
    | x == 0    = unsafeCoerce Zero
    | otherwise = unsafeCoerce (Succ (SNat (x - 1)))

type family (n :: Nat) + (m :: Nat) :: Nat where
  Z + m = m
  (S n) + m = S (n + m)

type family (n :: Nat) - (m :: Nat) :: Nat where
  Z - m = Z
  n - Z = n
  (S n) - (S m) = n - m

type family (n :: Nat) * (m :: Nat) :: Nat where
  Z * m = Z
  (S n) * m = m + (n * m)

type family SignumNat (n :: Nat) :: Nat where
  SignumNat Z = Z
  SignumNat (S n) = S Z

instance PNum ('Proxy :: Proxy Nat) where
  type n :+ m = n + m
  type n :- m = n - m
  type n :* m = n * m
  type Negate n = Error "Cannot Negate a Natural Number"
  type Abs n = n
  type Signum n = SignumNat n
  type FromInteger n = Lit n

instance SNum Nat where
  (SNat n) %:+ (SNat m) = SNat (n + m)
  (SNat n) %:- (SNat m)
    | m <= n    = SNat (n - m)
    | otherwise = SNat 0
  (SNat n) %:* (SNat m) = SNat (n * m)
  sNegate _ = error "Cannot call sNegate on a natural number singleton."
  sAbs n = n
  sSignum (SNat n)
    | n == 0    = SNat n
    | otherwise = SNat 1
  sFromInteger = SNat . fromIntegral . fromSing

type family EqualsNat (n :: Nat) (m :: Nat) :: Bool where
  EqualsNat Z Z     = True
  EqualsNat (S n) Z = False
  EqualsNat Z (S m) = False
  EqualsNat (S n) (S m) = EqualsNat n m

type family NotEqualsNat (n :: Nat) (m :: Nat) :: Bool where
  NotEqualsNat Z Z     = False
  NotEqualsNat (S n) Z = True
  NotEqualsNat Z (S m) = True
  NotEqualsNat (S n) (S m) = NotEqualsNat n m

instance PEq ('Proxy :: Proxy Nat) where
  type n :== m = EqualsNat n m
  type n :/= m = NotEqualsNat n m

instance SEq Nat where
  (SNat n) %:== (SNat m)
    | n == m    = unsafeCoerce STrue
    | otherwise = unsafeCoerce SFalse
  (SNat n) %:/= (SNat m)
    | n /= m    = unsafeCoerce STrue
    | otherwise = unsafeCoerce SFalse

type family Cmp (n :: Nat) (m :: Nat) :: Ordering where
  Cmp Z Z     = EQ
  Cmp (S n) Z = GT
  Cmp Z (S m) = LT
  Cmp (S n) (S m) = Cmp n m

type family MinNat (n :: Nat) (m :: Nat) :: Nat where
  MinNat Z m     = Z
  MinNat (S n) Z = Z
  MinNat (S n) (S m) = S (MinNat n m)

type family MaxNat (n :: Nat) (m :: Nat) :: Nat where
  MaxNat Z m     = m
  MaxNat (S n) Z = S n
  MaxNat (S n) (S m) = S (MaxNat n m)

instance POrd ('Proxy :: Proxy Nat) where
  type Compare n m = Cmp n m
  type Min n m = MinNat n m
  type Max n m = MaxNat n m

instance SOrd Nat where
  sCompare (SNat n) (SNat m) = case compare n m of
    LT -> unsafeCoerce SLT
    EQ -> unsafeCoerce SEQ
    GT -> unsafeCoerce SGT
  sMin (SNat n) (SNat m) = SNat (min n m)
  sMax (SNat n) (SNat m) = SNat (max n m)

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
  FZ :: Fin (S n)
  FS :: Fin n -> Fin (S n)

newtype Bound (n :: Nat) = Bound Int deriving (Eq,Ord)

instance Show (Bound n) where
  show (Bound i) = show i

newtype instance Sing (f :: Fin n) = SFin Int

instance Show (Sing (f :: Fin n)) where
  show (SFin i) = show i

instance SDecide (Fin n) where
  (SFin n) %~ (SFin m)
    | n == m    = Proved (unsafeCoerce Refl)
    | otherwise = Disproved (\Refl -> error "Data.Singletons.SDecide (Fin n): Integer equality failed.")

instance SingKind (Fin n) where
  type DemoteRep (Fin n) = Bound n
  fromSing (SFin i) = Bound i
  toSing (Bound i) = SomeSing (SFin i)

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeInType #-}

module Data.Nat.Properties where

import Data.Kind (type Type)
import Data.Type.Equality ((:~:)(..))
import Unsafe.Coerce (unsafeCoerce)

import Data.Nat

data SRefl :: forall k (a :: k) (b :: k). a :~: b -> Type where
  SRefl :: SRefl 'Refl

replace :: SRefl (refl :: x :~: y) -> p x -> p y
replace SRefl p = p

type family Cong (f :: t -> t) (x :: c :~: b) :: f c :~: f d where
  Cong f 'Refl = 'Refl

cong :: forall f c b refl. SRefl (refl :: c :~: b) -> SRefl (Cong f refl :: f c :~: f b)
cong SRefl = SRefl

type family Sym (x :: (b :: t) :~: (c :: t)) :: c :~: b where
  Sym 'Refl = 'Refl

sym :: SRefl refl -> SRefl (Sym refl)
sym SRefl = SRefl

type family Trans (x :: (a :: t) :~: b) (y :: b :~: c) :: a :~: c where
  Trans 'Refl 'Refl = 'Refl

trans :: SRefl a -> SRefl b -> SRefl (Trans a b)
trans SRefl SRefl = SRefl

type family PlusAssoc (a :: Nat) (b :: Nat) (c :: Nat) :: ((a + b) + c) :~: (a + (b + c)) where
  PlusAssoc 'Z a b = 'Refl
  PlusAssoc ('S n) a b = Cong 'S (PlusAssoc n a b)

plusAssoc :: SNat n -> SNat m -> SNat o -> SRefl (PlusAssoc n m o)
plusAssoc x y z = case viewNat x of
  Zero -> SRefl
  Succ n -> cong (plusAssoc n y z)

type family PlusRightIdentity (a :: Nat) :: (a + 'Z) :~: a where
  PlusRightIdentity 'Z = 'Refl
  PlusRightIdentity ('S n) = Cong 'S (PlusRightIdentity n)

plusRightIdentity :: SNat n -> SRefl (PlusRightIdentity n)
plusRightIdentity x = case viewNat x of
  Zero -> SRefl
  Succ n -> cong (plusRightIdentity n)

type family PlusRightSucc (a :: Nat) (b :: Nat) :: (a + 'S b) :~: ('S (a + b)) where
  PlusRightSucc 'Z y = 'Refl
  PlusRightSucc ('S n) y = Cong 'S (PlusRightSucc n y)

plusRightSucc :: SNat n -> SNat m -> SRefl (PlusRightSucc n m)
plusRightSucc x y = case viewNat x of
  Zero -> SRefl
  Succ n -> cong (plusRightSucc n y)

type family PlusComm (a :: Nat) (b :: Nat) :: (a + b) :~: (b + a) where
  PlusComm 'Z b = Sym (PlusRightIdentity b)
  PlusComm ('S n) b = Trans (Cong 'S (PlusComm n b)) (Sym (PlusRightSucc b n))

plusComm :: SNat n -> SNat m -> SRefl (PlusComm n m)
plusComm x y = case viewNat x of
  Zero -> sym (plusRightIdentity y)
  Succ n -> trans (cong (plusComm n y)) (sym (plusRightSucc y n))

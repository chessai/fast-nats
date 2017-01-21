{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
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

type family (x :: (a :: t) :~: b) ~~ (y :: b :~: c) :: a :~: c where
  'Refl ~~ 'Refl = 'Refl

(~~) :: SRefl a -> SRefl b -> SRefl (a ~~ b)
SRefl ~~ SRefl = SRefl

type family Injective (f :: k -> k) (p :: f a :~: f b) :: (a :~: b) where
  Injective t 'Refl = 'Refl

injective :: forall f refl. SRefl refl -> SRefl (Injective f refl)
injective SRefl = SRefl

type family PlusAssoc (a :: Nat) (b :: Nat) (c :: Nat) :: (a + b) + c :~: a + (b + c) where
  PlusAssoc 'Z a b = 'Refl
  PlusAssoc ('S n) a b = Cong 'S (PlusAssoc n a b)

plusAssoc :: SNat n -> SNat m -> SNat o -> SRefl (PlusAssoc n m o)
plusAssoc x y z = case viewNat x of
  Zero -> SRefl
  Succ n -> cong (plusAssoc n y z)

type family PlusRightIdentity (a :: Nat) :: a + 'Z :~: a where
  PlusRightIdentity 'Z = 'Refl
  PlusRightIdentity ('S n) = Cong 'S (PlusRightIdentity n)

plusRightIdentity :: SNat n -> SRefl (PlusRightIdentity n)
plusRightIdentity x = case viewNat x of
  Zero -> SRefl
  Succ n -> cong (plusRightIdentity n)

type family PlusRightSucc (a :: Nat) (b :: Nat) :: a + 'S b :~: 'S (a + b) where
  PlusRightSucc 'Z y = 'Refl
  PlusRightSucc ('S n) y = Cong 'S (PlusRightSucc n y)

plusRightSucc :: SNat n -> SNat m -> SRefl (PlusRightSucc n m)
plusRightSucc x y = case viewNat x of
  Zero -> SRefl
  Succ n -> cong (plusRightSucc n y)

type family PlusComm (a :: Nat) (b :: Nat) :: a + b :~: b + a where
  PlusComm 'Z b = Sym (PlusRightIdentity b)
  PlusComm ('S n) b = (Cong 'S (PlusComm n b)) ~~ (Sym (PlusRightSucc b n))

plusComm :: SNat n -> SNat m -> SRefl (PlusComm n m)
plusComm x y = case viewNat x of
  Zero -> sym (plusRightIdentity y)
  Succ n -> cong (plusComm n y) ~~ sym (plusRightSucc y n)

type family PlusLeftCancel (left :: Nat) (right1 :: Nat) (right2 :: Nat)
  (p :: left + right1 :~: left + right2) :: right1 :~: right2 where
  PlusLeftCancel 'Z r1 r2 p = p
  PlusLeftCancel ('S n) r1 r2 p = PlusLeftCancel n r1 r2 (Injective 'S p)

plusLeftCancel :: SNat left -> SNat right1 -> SNat right2 ->
  SRefl refl -> SRefl (PlusLeftCancel left right1 right2 refl)
plusLeftCancel l r1 r2 p = case viewNat l of
  Zero -> p
  Succ n -> plusLeftCancel n r1 r2 (injective p)

type family PlusRightCancel (left1 :: Nat) (left2 :: Nat) (right :: Nat)
  (p :: left1 + right :~: left2 + right) :: left1 :~: left2 where
  PlusRightCancel l1 l2 'Z p = Sym (PlusRightIdentity l1) ~~ p ~~ PlusRightIdentity l2
  PlusRightCancel l1 l2 ('S n) p = PlusRightCancel l1 l2 n
    (Injective 'S (Sym (PlusRightSucc l1 n) ~~ p ~~ PlusRightSucc l2 n))

plusRightCancel :: SNat left1 -> SNat left2 -> SNat right ->
  SRefl refl -> SRefl (PlusRightCancel left1 left2 right refl)
plusRightCancel l1 l2 r p = case viewNat r of
  Zero -> sym (plusRightIdentity l1) ~~ p ~~ plusRightIdentity l2
  Succ n -> plusRightCancel l1 l2 n
    (injective (sym (plusRightSucc l1 n) ~~ p ~~ plusRightSucc l2 n))

type family MulRightIdentity (n :: Nat) :: n * 'Z :~: 'Z where
  MulRightIdentity 'Z = 'Refl
  MulRightIdentity ('S n) = MulRightIdentity n

mulRightIdentity :: SNat n -> SRefl (MulRightIdentity n)
mulRightIdentity x = case viewNat x of
  Zero -> SRefl
  (Succ n) -> mulRightIdentity n

-- type family Test (n :: Nat) (m :: Nat) :: ('S n * m) :~: (m + (n * m)) where
--   Test n m = 'Refl

-- type family Lemma (n :: Nat) (m :: Nat) :: 'S m + n + m + n * m :~: 'S n + 'S n * m where

-- type family MulRightSuccLeftSide (n :: Nat) (m :: Nat)
--   (p :: n * 'S m :~: n + (n * m)) :: ('S n * 'S m :~: 'S n + 'S n * m) where
--   MulRightSuccLeftSide n m p = Test n m ~~ Cong ((+) ('S m)) p

-- type family MulRightSucc (n :: Nat) (m :: Nat) :: n * 'S m :~: n + n * m where
--   MulRightSucc 'Z m = 'Refl
--   MulRightSucc ('S n) m = MulRightSuccLeftSide n m (MulRightSucc n m)

-- mulRightSucc :: SNat n -> SNat m -> SRefl (MulRightSucc n m)
-- mulRightSucc x y = undefined

-- type family MulComm (n :: Nat) (m :: Nat) :: (n * m) :~: (m * n) where
--   MulComm 'Z m = Sym (MulRightIdentity m)
--   MulComm ('S n) m = MulComm n m ~~ MulRightSucc n m


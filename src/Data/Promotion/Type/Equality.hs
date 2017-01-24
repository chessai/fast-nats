{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeInType #-}
module Data.Promotion.Type.Equality where

import Data.Kind (type Type)
import Data.Type.Equality ((:~:)(..))
import Data.Singletons (Sing,SingKind(..),SomeSing(..),SingI(..))
import Data.Singletons.Decide (SDecide(..),Decision(..))

data instance Sing (refl :: a :~: b) where
  SRefl :: Sing 'Refl

instance SingKind (a :~: b) where
  type DemoteRep (a :~: b) = a :~: b
  fromSing SRefl = Refl
  toSing Refl = SomeSing SRefl

instance SingI Refl where
  sing = SRefl

instance SDecide (a :~: b) where
  SRefl %~ SRefl = Proved Refl

type SRefl (refl :: a :~: b) = Sing refl

type family Sym (x :: (b :: t) :~: (c :: t)) :: c :~: b where
  Sym 'Refl = 'Refl

sym :: SRefl refl -> SRefl (Sym refl)
sym SRefl = SRefl

type family Trans (x :: (a :: t) :~: b) (y :: b :~: c) :: a :~: c where
  Trans Refl Refl = Refl

trans :: SRefl a -> SRefl b -> SRefl (Trans a b)
trans SRefl SRefl = SRefl

type (~~) a b = Trans a b

(~~) :: SRefl a -> SRefl b -> SRefl (a ~~ b)
(~~) = trans

type family CastWith (x :: a :~: b) (y :: a) :: b where
  CastWith Refl y = y

castWith :: SRefl refl -> p a -> p (CastWith refl a)
castWith SRefl y = y

-- I think i found a bug in ghc
-- type family GCastWith (x :: (a :: t) :~: (b :: t)) (y :: (a ~ b) => r) :: r where
  -- GCastWith Refl y = y
-- Errors with:
-- • Occurs check: cannot construct the infinite kind:
--     r0 ~ b0 ~ b0 => r0
-- • In the type ‘y’
--   In the type family declaration for ‘GCastWith’
-- • Type variable kinds: b0 :: t0


type family Apply (x :: (f :: k -> j) :~: g) (y :: (a :: k) :~: b) :: f a :~: g b where
  Apply Refl Refl = Refl

apply :: SRefl f -> SRefl x -> SRefl (Apply f x)
apply SRefl SRefl = SRefl

type family Cong (x :: (a :: k) :~: b) :: (f :: k -> j) a :~: f b where
  Cong Refl = Refl

cong :: SRefl refl -> SRefl (Cong Refl)
cong SRefl = SRefl

type family Inner (x :: (f :: k -> j) a :~: g b) :: a :~: b where
  Inner Refl = Refl

inner :: SRefl refl -> SRefl (Inner refl)
inner SRefl = SRefl

type family Outer (x :: (f :: k -> j) a :~: g b) :: f :~: g where
  Outer Refl = Refl

outer :: SRefl refl -> SRefl (Outer refl)
outer SRefl = SRefl

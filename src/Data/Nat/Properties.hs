{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unticked-promoted-constructors #-}
module Data.Nat.Properties where

import Data.Type.Equality ((:~:)(..),sym,trans,inner)
import Data.Viewable (Viewable(..))
import Data.Nat (type Nat(..),type SNat,View(..))
import Data.Singletons.Prelude.Num (PNum(..))

cong :: forall f a b. a :~: b -> f a :~: f b
cong Refl = Refl

plusAssoc :: SNat n -> SNat m -> SNat o -> (n :+ m) :+ o :~: n :+ (m :+ o)
plusAssoc x y z = case view x of
  Zero -> Refl
  Succ n -> cong (plusAssoc n y z)

plusRightIdentity :: SNat n -> n :+ Z :~: n
plusRightIdentity x = case view x of
  Zero -> Refl
  Succ n -> cong (plusRightIdentity n)

plusRightSucc :: SNat n -> SNat m -> n :+ S m :~: S (n :+ m)
plusRightSucc x y = case view x of
  Zero -> Refl
  Succ n -> cong (plusRightSucc n y)

plusComm :: SNat n -> SNat m -> n :+ m :~: m :+ n
plusComm x y = case view x of
  Zero -> sym (plusRightIdentity y)
  Succ n -> cong (plusComm n y) `trans` sym (plusRightSucc y n)

plusLeftCancel ::
  SNat left -> SNat right1 -> SNat right2 ->
  left :+ right1 :~: left :+ right2 -> right1 :~: right2
plusLeftCancel l r1 r2 p = case view l of
  Zero -> p
  Succ n -> plusLeftCancel n r1 r2 (inner p)

plusRightCancel ::
  SNat left1 -> SNat left2 -> SNat right ->
  left1 :+ right :~: left2 :+ right -> left1 :~: left2
plusRightCancel l1 l2 r p = plusLeftCancel r l1 l2 (plusComm r l1 `trans` p `trans` sym (plusComm r l2))

mulRightIdentity :: SNat n -> n :* Z :~: Z
mulRightIdentity x = case view x of
  Zero -> Refl
  Succ n -> mulRightIdentity n

-- mulRightSucc :: forall n m. SNat n -> SNat m -> n :* S m :~: n :+ (n :* m)
-- mulRightSucc x y = case view x of
--   Zero -> Refl

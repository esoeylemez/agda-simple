-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Algebra.Group where

open import Algebra.Groupoid
open import Algebra.Monoid
open import Core


-- A group is a monoid where all elements are invertible.

record GroupOver {a r} (A : Set a) (Eq : Equiv {r = r} A) : Set (a ⊔ r) where
  field monoidOver : MonoidOver A Eq
  open MonoidOver monoidOver public

  field
    inv : A → A
    inv-cong : ∀ {x y} → x ≈ y → inv x ≈ inv y
    left-inv : ∀ x → inv x ⋄ x ≈ id

  groupoid : Groupoid
  groupoid =
    record {
      category = category;
      inv = inv;
      inv-cong = inv-cong;
      left-inv = left-inv
    }

record Group {a r} : Set (lsuc (a ⊔ r)) where
  field
    A : Set a
    Eq : Equiv {r = r} A
    groupOver : GroupOver A Eq

  open GroupOver groupOver public

  monoid : Monoid
  monoid =
    record {
      A = A;
      Eq = Eq;
      monoidOver = monoidOver
    }

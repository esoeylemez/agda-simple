-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Algebra.Group where

open import Algebra.Monoid
open import Algebra.Groupoid
open import Core


-- A group is a monoid where all elements are invertible.

record Group {a} {r} : Set (lsuc (a ⊔ r)) where
  field monoid : Monoid {a} {r}
  open Monoid monoid public

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

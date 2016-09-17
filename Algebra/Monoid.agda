-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Algebra.Monoid where

open import Algebra.Category
open import Algebra.Groupoid
open import Algebra.Relation
open import Algebra.Semigroup
open import Core


record Monoid {a} {r} : Set (lsuc (a ⊔ r)) where
  field semigroup : Semigroup {a} {r}
  open Semigroup semigroup public

  field
    id : A
    left-id  : ∀ {x} → id ⋄ x ≈ x
    right-id : ∀ {x} → x ⋄ id ≈ x

  category : Category
  category =
    record {
      semigroupoid = semigroupoid;
      id = id;
      left-id = left-id;
      right-id = right-id
    }

  open Category category public
    using (id-unique)


record Group {a} {r} : Set (lsuc (a ⊔ r)) where
  field monoid : Monoid {a} {r}
  open Monoid monoid public

  field
    inv : A → A
    inv-cong : ∀ {x y} → x ≈ y → inv x ≈ inv y
    left-inv : ∀ {x} → inv x ⋄ x ≈ id

  groupoid : Groupoid
  groupoid =
    record {
      category = category;
      inv = inv;
      inv-cong = inv-cong;
      left-inv = left-inv
    }

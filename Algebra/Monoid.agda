-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Algebra.Monoid where

open import Algebra.Category
open import Algebra.Relation
open import Algebra.Semigroup
open import Core


-- A monoid is a semigroup with an identity element.

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

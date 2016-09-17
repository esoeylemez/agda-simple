-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Algebra.Semigroup where

open import Algebra.Relation
open import Algebra.Semigroupoid
open import Core


record Semigroup {a} {r} : Set (lsuc (a ⊔ r)) where
  field
    A  : Set a
    Eq : Equiv r A

  open Equiv Eq public

  field
    _⋄_ : A → A → A
    ⋄-cong : ∀ {x1 x2 y1 y2} → x1 ≈ x2 → y1 ≈ y2 → x1 ⋄ y1 ≈ x2 ⋄ y2
    assoc  : ∀ {x y z} → (x ⋄ y) ⋄ z ≈ x ⋄ (y ⋄ z)

  semigroupoid : Semigroupoid
  semigroupoid =
    record {
      Ob = ⊤;
      Hom = λ _ _ → A;
      Eq = Eq;
      _∘_ = _⋄_;
      ∘-cong = ⋄-cong;
      assoc = assoc
    }

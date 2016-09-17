-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Algebra.Semigroup where

open import Algebra.Relation
open import Algebra.Semigroupoid
open import Core


-- A semigroup is an associative binary function.

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


-- A semigroup morphism is a function that maps the elements of one
-- semigroup to another while preserving the compositional structure.

record SemigroupMorphism
       {sa sr ta tr}
       (S : Semigroup {sa} {sr})
       (T : Semigroup {ta} {tr})
       : Set (sa ⊔ ta ⊔ sr ⊔ tr)
       where

  private
    module S = Semigroup S
    module T = Semigroup T

  field
    map : S.A → T.A
    map-cong : ∀ {x y} → x S.≈ y → map x T.≈ map y
    ⋄-preserving : ∀ {x y} → map (x S.⋄ y) T.≈ map x T.⋄ map y

  semifunctor : Semifunctor S.semigroupoid T.semigroupoid
  semifunctor =
    record {
      F = λ _ → tt;
      map = map;
      map-cong = map-cong;
      ∘-preserving = ⋄-preserving
    }

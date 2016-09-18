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
    left-id  : ∀ x → id ⋄ x ≈ x
    right-id : ∀ x → x ⋄ id ≈ x

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


-- A monoid morphism is a semigroup morphism that also preserves
-- identities.

record MonoidMorphism
       {sa sr ta tr}
       (M : Monoid {sa} {sr})
       (N : Monoid {ta} {tr})
       : Set (sa ⊔ ta ⊔ sr ⊔ tr)
       where

  private
    module M = Monoid M
    module N = Monoid N

  field semigroupMorphism : SemigroupMorphism M.semigroup N.semigroup
  open SemigroupMorphism semigroupMorphism public

  field
    id-preserving : map M.id N.≈ N.id

  functor : Functor M.category N.category
  functor =
    record {
      semifunctor = semifunctor;
      id-preserving = id-preserving
    }


-- An equivalence relation on monoid morphisms.

MonoidMorphismEq :
  ∀ {ma mr na nr}
    {M : Monoid {ma} {mr}} {N : Monoid {na} {nr}}
  → Equiv _ (MonoidMorphism M N)
MonoidMorphismEq {N = N} =
  record {
    _≈_ = λ F G →
            let module F = MonoidMorphism F
                module G = MonoidMorphism G
            in ∀ x → F.map x ≈ G.map x;
    refl = λ _ → refl;
    sym = λ x≈y x → sym (x≈y x);
    trans = λ x≈y y≈z x → trans (x≈y x) (y≈z x)
  }

  where
  module N = Monoid N
  open Equiv N.Eq

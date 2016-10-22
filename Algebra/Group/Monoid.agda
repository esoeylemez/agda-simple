-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Algebra.Group.Monoid where

open import Algebra.Category
open import Algebra.Group.Semigroup
open import Core


-- A monoid is a semigroup with an identity element.

record IsMonoid {a r} (S : Semigroup {a} {r}) : Set (a ⊔ r) where
  open Semigroup S

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
    using (id-unique; Iso)


record Monoid {a r} : Set (lsuc (a ⊔ r)) where
  field
    semigroup : Semigroup {a} {r}
    isMonoid  : IsMonoid semigroup

  open Semigroup semigroup public
  open IsMonoid isMonoid public


-- A monoid morphism is a function that maps the elements of one monoid
-- to another while preserving the compositional structure as well as
-- identity.

record MonoidMorphism
           {ma mr na nr}
           (M : Monoid {ma} {mr})
           (N : Monoid {na} {nr})
           : Set (ma ⊔ mr ⊔ na ⊔ nr)
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

  open Functor functor public
    using (Iso-preserving)


-- An equivalence relation on monoid morphisms that considers monoid
-- morphisms to be equal iff they map every element in the domain to the
-- same element in the codomain.

MonoidMorphismEq :
  ∀ {ma mr na nr}
    {M : Monoid {ma} {mr}} {N : Monoid {na} {nr}}
  → Equiv (MonoidMorphism M N)
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

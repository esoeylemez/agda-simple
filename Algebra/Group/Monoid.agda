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


-- Category of monoids.

Monoids : ∀ {a r} → Category
Monoids {a} {r} =
  record {
    semigroupoid = record {
      Ob = Monoid {a} {r};
      Hom = MonoidMorphism;
      Eq = MonoidMorphismEq;
      _∘_ = _∘_;
      ∘-cong = λ {_} {_} {_} {f1} {f2} {g1} {g2} → ∘-cong {f1 = f1} {f2} {g1} {g2};
      assoc = assoc
    };
    id = id;
    left-id = left-id;
    right-id = right-id
  }

  where
  open module MyEquiv {M : Monoid} {N : Monoid} = Equiv (MonoidMorphismEq {M = M} {N})

  id : ∀ {M} → MonoidMorphism M M
  id {M} =
    record {
      semigroupMorphism = record {
        map = SetC.id;
        map-cong = SetC.id;
        ⋄-preserving = λ x y → M.refl
      };
      id-preserving = M.refl
    }

    where
    module M = Monoid M

  _∘_ : ∀ {M N O} → MonoidMorphism N O → MonoidMorphism M N → MonoidMorphism M O
  _∘_ {M} {N} {O} f g =
    record {
      semigroupMorphism = f.semigroupMorphism Semigroups.∘ g.semigroupMorphism;
      id-preserving =
        O.begin
          f.map (g.map M.id) O.≈[ f.map-cong g.id-preserving ]
          f.map N.id         O.≈[ f.id-preserving ]
          O.id
        O.qed
    }

    where
    module f = MonoidMorphism f
    module g = MonoidMorphism g
    module M = Monoid M
    module N = Monoid N
    module O = Monoid O

  ∘-cong :
    ∀ {M N O}
      {f1 f2 : MonoidMorphism N O}
      {g1 g2 : MonoidMorphism M N}
    → f1 ≈ f2
    → g1 ≈ g2
    → f1 ∘ g1 ≈ f2 ∘ g2
  ∘-cong {O = O} {f1} {f2} {g1} {g2} f1≈f2 g1≈g2 x =
    O.begin
      f1.map (g1.map x) O.≈[ f1.map-cong (g1≈g2 x) ]
      f1.map (g2.map x) O.≈[ f1≈f2 (g2.map x) ]
      f2.map (g2.map x)
    O.qed

    where
    module O = Monoid O
    module f1 = MonoidMorphism f1
    module f2 = MonoidMorphism f2
    module g1 = MonoidMorphism g1
    module g2 = MonoidMorphism g2

  assoc :
    ∀ {M N O P}
      (f : MonoidMorphism O P)
      (g : MonoidMorphism N O)
      (h : MonoidMorphism M N)
    → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
  assoc {P = P} _ _ _ _ = P.refl
    where
    module P = Monoid P

  left-id : ∀ {M N} (f : MonoidMorphism M N) → id ∘ f ≈ f
  left-id {N = N} _ _ = N.refl
    where
    module N = Monoid N

  right-id : ∀ {M N} (f : MonoidMorphism M N) → f ∘ id ≈ f
  right-id {N = N} _ _ = N.refl
    where
    module N = Monoid N

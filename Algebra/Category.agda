-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Algebra.Category where

open import Algebra.Relation
open import Core
open import Equality


-- A semigroupoid is a set of objects and morphisms between objects
-- together with an associative binary function that combines morphisms.

record Semigroupoid {c h r} : Set (lsuc (c ⊔ h ⊔ r)) where
  field
    Ob  : Set c
    Hom : Ob → Ob → Set h
    Eq  : ∀ {A B} → Equiv r (Hom A B)
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

  infixl 6 _∘_

  open module MyEquiv {A} {B} = Equiv (Eq {A} {B}) public

  field
    ∘-cong :
      ∀ {A B C}
        {f1 f2 : Hom B C} {g1 g2 : Hom A B}
      → f1 ≈ f2 → g1 ≈ g2 → f1 ∘ g1 ≈ f2 ∘ g2

    assoc :
      ∀ {A B C D}
        {f : Hom C D} {g} {h : Hom A B}
      → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)


-- A category is a semigroupoid with an identity morphism on every
-- object.

record Category {c h r} : Set (lsuc (c ⊔ h ⊔ r)) where
  field semigroupoid : Semigroupoid {c} {h} {r}
  open Semigroupoid semigroupoid public

  field
    id : ∀ {A} → Hom A A
    left-id  : ∀ {A B} {f : Hom A B} → id ∘ f ≈ f
    right-id : ∀ {A B} {f : Hom A B} → f ∘ id ≈ f

  open Reasoning

  -- The identity morphism is unique for each object.
  id-unique :
    ∀ {A} (id' : Hom A A)
    → id' ∘ id ≈ id
    → id' ≈ id
  id-unique id' left-id' =
    begin
      id'      || sym right-id ::
      id' ∘ id || left-id' ::
      id
    qed


-- -- A groupoid is a category where all morphisms are isomorphisms.

record Groupoid {c h r} : Set (lsuc (c ⊔ h ⊔ r)) where
  field category : Category {c} {h} {r}
  open Category category public

  field
    inv : ∀ {A B} → Hom A B → Hom B A
    inv-cong : ∀ {A B} {f g : Hom A B} → f ≈ g → inv f ≈ inv g
    left-inv : ∀ {A B} {f : Hom A B} → inv f ∘ f ≈ id

  open Reasoning

  -- Inverses are unique for each morphism.
  inv-unique : ∀ {A B} {inv-f' : Hom A B} {f} → f ∘ inv-f' ≈ id → inv-f' ≈ inv f
  inv-unique {inv-f' = inv-f'} {f = f} right-inv' =
    begin
      inv-f'               || sym left-id ::
      id ∘ inv-f'          || ∘-cong (sym left-inv) refl ::
      (inv f ∘ f) ∘ inv-f' || assoc ::
      inv f ∘ (f ∘ inv-f') || ∘-cong refl right-inv' ::
      inv f ∘ id           || right-id ::
      inv f
    qed

  -- The inverse function is an involution.
  inv-invol : ∀ {A B} {f : Hom A B} → inv (inv f) ≈ f
  inv-invol {f = f} =
    begin
      inv (inv f)               || sym right-id ::
      inv (inv f) ∘ id          || ∘-cong refl (sym left-inv) ::
      inv (inv f) ∘ (inv f ∘ f) || sym assoc ::
      (inv (inv f) ∘ inv f) ∘ f || ∘-cong left-inv refl ::
      id ∘ f                    || left-id ::
      f
    qed

  -- The right-inverses law follows from the groupoid axioms.
  right-inv : ∀ {A B} {f : Hom A B} → f ∘ inv f ≈ id
  right-inv {f = f} =
    begin
      f ∘ inv f           || ∘-cong (sym inv-invol) refl ::
      inv (inv f) ∘ inv f || left-inv ::
      id
    qed


-- A functor is a structure-preserving mapping from one category to
-- another.

record Functor {cc ch cr dc dh dr}
               (C : Category {cc} {ch} {cr})
               (D : Category {dc} {dh} {dr})
               : Set (cc ⊔ ch ⊔ cr ⊔ dc ⊔ dh ⊔ dr) where
  module C = Category C
  module D = Category D

  field
    mapOb : C.Ob → D.Ob
    map : ∀ {A B} → C.Hom A B → D.Hom (mapOb A) (mapOb B)

    id-preserve : ∀ {A} → map (C.id {A}) D.≈ D.id {mapOb A}

    ∘-preserve :
      ∀ {A B C}
        {f : C.Hom B C} {g : C.Hom A B}
      → map (f C.∘ g) D.≈ map f D.∘ map g

    map-cong :
      ∀ {A B} {f g : C.Hom A B}
      → f C.≈ g → map f D.≈ map g


-- Category of types and functions.

SetC : ∀ r → Category
SetC r =
  record {
    semigroupoid = record {
      Ob = Set r;
      Hom = λ A B → A → B;
      Eq = λ {A B} → PropFuncEq A B;
      _∘_ = _∘_;
      ∘-cong = ∘-cong;
      assoc = λ _ → P.refl
    };
    id = λ x → x;
    left-id = λ _ → P.refl;
    right-id = λ _ → P.refl
  }

  where
  open module MyEquiv {A} {B} = Equiv (PropFuncEq A B)
  module P {A} = Equiv (PropEq A)

  _∘_ : {A B C : Set r} (f : B → C) (g : A → B) → A → C
  (f ∘ g) x = f (g x)

  infixl 6 _∘_

  ∘-cong :
    ∀ {A B C}
      {f1 f2 : B → C} {g1 g2 : A → B}
    → f1 ≈ f2 → g1 ≈ g2 → f1 ∘ g1 ≈ f2 ∘ g2
  ∘-cong {f1 = f1} f1≈f2 g1≈g2 x =
    P.trans (cong f1 (g1≈g2 _)) (f1≈f2 _)

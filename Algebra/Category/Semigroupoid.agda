-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Algebra.Category.Semigroupoid where

open import Core


-- A semigroupoid is a set of objects and morphisms between objects
-- together with an associative binary function that combines morphisms.

record Semigroupoid {c h r} : Set (lsuc (c ⊔ h ⊔ r)) where
  field
    Ob  : Set c
    Hom : Ob → Ob → Set h
    Eq  : ∀ {A B} → Equiv {r = r} (Hom A B)
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
        (f : Hom C D) (g : Hom B C) (h : Hom A B)
      → (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)

  Epic : ∀ {A B} → (f : Hom A B) → Set _
  Epic f = ∀ {C} {g1 g2 : Hom _ C} → g1 ∘ f ≈ g2 ∘ f → g1 ≈ g2

  Monic : ∀ {B C} → (f : Hom B C) → Set _
  Monic f = ∀ {A} {g1 g2 : Hom A _} → f ∘ g1 ≈ f ∘ g2 → g1 ≈ g2

  Unique : ∀ {A B} → (f : Hom A B) → Set _
  Unique f = ∀ g → f ≈ g

  IsProduct : ∀ A B AB → (fst : Hom AB A) (snd : Hom AB B) → Set _
  IsProduct A B AB fst snd =
    ∀ AB' (fst' : Hom AB' A) (snd' : Hom AB' B) →
    ∃ (λ (u : Hom AB' AB) → Unique u × (fst ∘ u ≈ fst') × (snd ∘ u ≈ snd'))

  record Product A B : Set (c ⊔ h ⊔ r) where
    field
      A×B  : Ob
      cfst : Hom A×B A
      csnd : Hom A×B B
      isProduct : IsProduct A B A×B cfst csnd

  record _bimonic_ A B : Set (c ⊔ h ⊔ r) where
    field
      to   : Hom A B
      from : Hom B A
      to-monic   : Monic to
      from-monic : Monic from


-- A semifunctor is a composition-preserving mapping from a semigroupoid
-- to another.

record Semifunctor
           {cc ch cr dc dh dr}
           (C : Semigroupoid {cc} {ch} {cr})
           (D : Semigroupoid {dc} {dh} {dr})
           : Set (cc ⊔ ch ⊔ cr ⊔ dc ⊔ dh ⊔ dr)
       where

  private
    module C = Semigroupoid C
    module D = Semigroupoid D

  field
    F   : C.Ob → D.Ob
    map : ∀ {A B} → C.Hom A B → D.Hom (F A) (F B)

    map-cong :
      ∀ {A B} {f g : C.Hom A B}
      → f C.≈ g
      → map f D.≈ map g

    ∘-preserving :
      ∀ {A B C}
        (f : C.Hom B C) (g : C.Hom A B)
      → map (f C.∘ g) D.≈ map f D.∘ map g

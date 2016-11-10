-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Algebra.Category.Category where

open import Algebra.Category.Semigroupoid
open import Core


-- A category is a semigroupoid with an identity morphism on every
-- object.

record Category {c h r} : Set (lsuc (c ⊔ h ⊔ r)) where
  field semigroupoid : Semigroupoid {c} {h} {r}
  open Semigroupoid semigroupoid public

  field
    id : ∀ {A} → Hom A A
    left-id  : ∀ {A B} (f : Hom A B) → id ∘ f ≈ f
    right-id : ∀ {A B} (f : Hom A B) → f ∘ id ≈ f

  -- The identity morphism is unique for each object.
  id-unique :
    ∀ {A} {id' : Hom A A}
    → id' ∘ id ≈ id
    → id' ≈ id
  id-unique {id' = id'} left-id' =
    begin
      id'      ≈[ sym (right-id _) ]
      id' ∘ id ≈[ left-id' ]
      id
    qed

  -- Isomorphisms
  record Iso {A B} (f : Hom A B) : Set (h ⊔ r) where
    field
      inv : Hom B A
      left-inv  : inv ∘ f ≈ id
      right-inv : f ∘ inv ≈ id

    -- Inverses are unique for each morphism.
    inv-unique : ∀ g → f ∘ g ≈ id → g ≈ inv
    inv-unique g right-inv' =
      begin
        g              ≈[ sym (left-id g) ]
        id ∘ g         ≈[ ∘-cong (sym left-inv) refl ]
        (inv ∘ f) ∘ g  ≈[ assoc inv f g ]
        inv ∘ (f ∘ g)  ≈[ ∘-cong refl right-inv' ]
        inv ∘ id       ≈[ right-id inv ]
        inv
      qed

    inv-iso : Iso inv
    inv-iso =
      record {
        inv = f;
        left-inv = right-inv;
        right-inv = left-inv
      }

    inv-invol : ∀ g h → g ∘ f ≈ id → h ∘ g ≈ id → f ≈ h
    inv-invol g h g-left-inv h-left-inv =
      begin
        f            ≈[ sym (left-id f) ]
        id ∘ f       ≈[ ∘-cong (sym h-left-inv) refl ]
        (h ∘ g) ∘ f  ≈[ assoc h g f ]
        h ∘ (g ∘ f)  ≈[ ∘-cong refl g-left-inv ]
        h ∘ id       ≈[ right-id h ]
        h
      qed


-- A functor is a structure-preserving mapping from one category to
-- another.

record Functor
           {cc ch cr dc dh dr}
           (C : Category {cc} {ch} {cr})
           (D : Category {dc} {dh} {dr})
           : Set (cc ⊔ ch ⊔ cr ⊔ dc ⊔ dh ⊔ dr)
       where

  private
    module C = Category C
    module D = Category D

  field semifunctor : Semifunctor C.semigroupoid D.semigroupoid
  open Semifunctor semifunctor public

  field
    id-preserving : ∀ {A} → map (C.id {A}) D.≈ D.id {F A}

  Iso-preserving : ∀ {A B} {f : C.Hom A B} → C.Iso f → D.Iso (map f)
  Iso-preserving {f = f} p =
    record {
      inv = map inv;
      left-inv =
        D.begin
          map inv D.∘ map f  D.≈[ D.sym (∘-preserving inv f) ]
          map (inv C.∘ f)    D.≈[ map-cong left-inv ]
          map C.id           D.≈[ id-preserving ]
          D.id
        D.qed;
      right-inv =
        D.begin
          map f D.∘ map inv  D.≈[ D.sym (∘-preserving f inv) ]
          map (f C.∘ inv)    D.≈[ map-cong right-inv ]
          map C.id           D.≈[ id-preserving ]
          D.id
        D.qed
    }

    where
    open Category.Iso p


-- Category of types and functions.

Sets : ∀ {r} → Category
Sets {r} =
  record {
    semigroupoid = record {
      Ob = Set r;
      Hom = λ A B → A → B;
      Eq = λ {A B} → PropFuncEq A B;
      _∘_ = _∘_;
      ∘-cong = ∘-cong;
      assoc = λ _ _ _ _ → P.refl
    };
    id = λ x → x;
    left-id = λ _ _ → P.refl;
    right-id = λ _ _ → P.refl
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

module Sets {r} = Category (Sets {r})


injective→monic :
  ∀ {a} {A B : Set a}
    {f : A → B}
  → (∀ {x y} → f x ≡ f y → x ≡ y)
  → Sets.Monic f
injective→monic inj p x = inj (p x)


monic→injective :
  ∀ {a} {A B : Set a}
    {f : A → B}
  → Sets.Monic f
  → ∀ {x y} → f x ≡ f y → x ≡ y
monic→injective monic p = monic Sets.id p

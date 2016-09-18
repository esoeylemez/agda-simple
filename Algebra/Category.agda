-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Algebra.Category where

open import Algebra.Semigroupoid
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
      id'      || sym (right-id _) ::
      id' ∘ id || left-id' ::
      id
    qed


-- A functor is a structure-preserving mapping from one category to
-- another.

record Functor {cc ch cr dc dh dr}
               (C : Category {cc} {ch} {cr})
               (D : Category {dc} {dh} {dr})
               : Set (cc ⊔ ch ⊔ cr ⊔ dc ⊔ dh ⊔ dr) where

  private
    module C = Category C
    module D = Category D

  field semifunctor : Semifunctor C.semigroupoid D.semigroupoid
  open Semifunctor semifunctor public

  field
    id-preserving : ∀ {A} → map (C.id {A}) D.≈ D.id {F A}


-- Category of types and functions.

SetC : ∀ {r} → Category
SetC {r} =
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

module SetC {r} = Category (SetC {r})

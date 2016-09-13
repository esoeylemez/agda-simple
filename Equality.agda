-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Equality where

open import Agda.Builtin.Equality
open import Algebra.Relation
open import Core


PropEq : ∀ {a} → (A : Set a) → Equiv _ A
PropEq A =
  record {
    _≈_ = _≡_;
    refl = refl;
    sym = sym';
    trans = trans'
  }

  where
  sym' : {x y : A} → x ≡ y → y ≡ x
  sym' refl = refl

  trans' : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans' refl q = q


PropFuncEq : ∀ {a b} (A : Set a) (B : Set b) → Equiv _ (A → B)
PropFuncEq A B =
  record {
    _≈_ = λ f g → ∀ x → f x ≡ g x;
    refl = λ _ → refl;
    sym = λ p x → P.sym (p x);
    trans = λ p q x → P.trans (p x) (q x)
  }

  where
  module P = Equiv (PropEq B)


cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong _ refl = refl


cong2 :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
    (f : A → B → C)
  → ∀ {x1 x2 : A} {y1 y2 : B}
    → x1 ≡ x2
    → y1 ≡ y2
    → f x1 y1 ≡ f x2 y2
cong2 _ refl refl = refl

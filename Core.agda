-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>
--
-- This module contains definitions that are fundamental and/or used
-- everywhere.

module Core where

open import Agda.Builtin.Equality public
  renaming (refl to ≡-refl)
  using (_≡_)
open import Agda.Builtin.FromNat public
open import Agda.Builtin.FromNeg public
open import Agda.Builtin.FromString public
open import Agda.Builtin.Unit using (⊤; tt) public
open import Agda.Primitive using (Level; lsuc; lzero; _⊔_) public


-- An empty type (or a false hypothesis).

data ⊥ : Set where


-- Dependent sums (or existential quantification).

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infixr 4 _,_

∃ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
∃ = Σ _

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ A (λ _ → B)

infixr 7 _×_


-- Equivalence relations.

record Equiv {a r} (A : Set a) : Set (a ⊔ lsuc r) where
  field
    _≈_   : A → A → Set r
    refl  : ∀ {x} → x ≈ x
    sym   : ∀ {x y} → x ≈ y → y ≈ x
    trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

  infix 4 _≈_

  -- Helper functions for equational reasoning.
  begin_ : ∀ {x y} → x ≈ y → x ≈ y
  begin_ p = p

  _||_::_ : ∀ x {y z} → x ≈ y → y ≈ z → x ≈ z
  _ || x≈y :: y≈z = trans x≈y y≈z

  _|:_ : ∀ x {y} → x ≈ y → x ≈ y
  _ |: p = p

  _qed : ∀ (x : A) → x ≈ x
  _qed _ = refl

  infix  1 begin_
  infixr 2 _||_::_ _|:_
  infix  3 _qed

PropEq : ∀ {a} → (A : Set a) → Equiv A
PropEq A =
  record {
    _≈_ = _≡_;
    refl = ≡-refl;
    sym = sym';
    trans = trans'
  }

  where
  sym' : ∀ {x y} → x ≡ y → y ≡ x
  sym' ≡-refl = ≡-refl

  trans' : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
  trans' ≡-refl q = q

PropFuncEq : ∀ {a b} (A : Set a) (B : Set b) → Equiv (A → B)
PropFuncEq A B =
  record {
    _≈_ = λ f g → ∀ x → f x ≡ g x;
    refl = λ _ → ≡-refl;
    sym = λ p x → P.sym (p x);
    trans = λ p q x → P.trans (p x) (q x)
  }

  where
  module P = Equiv (PropEq B)

cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong _ ≡-refl = ≡-refl

cong2 :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
    (f : A → B → C)
  → ∀ {x1 x2 : A} {y1 y2 : B}
    → x1 ≡ x2
    → y1 ≡ y2
    → f x1 y1 ≡ f x2 y2
cong2 _ ≡-refl ≡-refl = ≡-refl


-- Low-priority function application.

_$_ : ∀ {a} {A : Set a} → A → A
_$_ f = f

infixr 0 _$_


-- Given two predicates, this is the predicate that requires both.

_and_ : ∀ {a r1 r2} {A : Set a} → (A → Set r1) → (A → Set r2) → A → Set (r1 ⊔ r2)
(P and Q) x = P x × Q x

infixr 6 _and_


-- Use instance resolution to find a value of the target type.

it : ∀ {a} {A : Set a} {{_ : A}} → A
it {{x}} = x


-- Values with inline type signatures.

the : ∀ {a} (A : Set a) → A → A
the _ x = x

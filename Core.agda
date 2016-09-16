-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>
--
-- This module contains definitions that are fundamental and/or used
-- everywhere.

module Core where

open import Agda.Builtin.FromNat public
open import Agda.Builtin.Unit using (⊤; tt) public
open import Agda.Primitive using (Level; lsuc; lzero; _⊔_) public


data ⊥ : Set where


data Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  _,_ : (x : A) → (p : B x) → Σ A B

infixr 4 _,_

∃ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
∃ = Σ _

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ A (λ _ → B)

infixr 7 _×_


_$_ : ∀ {a} {A : Set a} → A → A
_$_ f = f

infixr 0 _$_


it : ∀ {a} {A : Set a} {{_ : A}} → A
it {{x}} = x


the : ∀ {a} (A : Set a) → A → A
the _ x = x

-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Algebra.Relation where

open import Core


Rel : ∀ {a} r (A : Set a) → Set (a ⊔ lsuc r)
Rel r A = A → A → Set r


record Equiv {a} r (A : Set a) : Set (a ⊔ lsuc r) where
  field
    _≈_   : Rel r A
    refl  : ∀ {x} → x ≈ x
    sym   : ∀ {x y} → x ≈ y → y ≈ x
    trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

  infix 4 _≈_

  module Reasoning where
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

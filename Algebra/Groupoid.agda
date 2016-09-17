-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Algebra.Groupoid where

open import Algebra.Category
open import Core


-- A groupoid is a category where all morphisms are isomorphisms.

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

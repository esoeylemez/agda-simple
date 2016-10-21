-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Algebra.Category.Groupoid where

open import Algebra.Category.Category
open import Core


-- A groupoid is a category where all morphisms are isomorphisms.

record Groupoid {c h r} : Set (lsuc (c ⊔ h ⊔ r)) where
  field category : Category {c} {h} {r}
  open Category category public

  field iso : ∀ {A B} (f : Hom A B) → Iso f
  open module MyIso {A B} (f : Hom A B) = Iso (iso f) public
       using (inv; left-inv; right-inv; inv-unique)

  field
    inv-cong : ∀ {A B} {f g : Hom A B} → f ≈ g → inv f ≈ inv g

  -- The inverse function is an involution.
  inv-invol : ∀ {A B} {f : Hom A B} → inv (inv f) ≈ f
  inv-invol {f = f} =
    begin
      inv (inv f)               ≈[ sym (right-id _) ]
      inv (inv f) ∘ id          ≈[ ∘-cong refl (sym (left-inv _)) ]
      inv (inv f) ∘ (inv f ∘ f) ≈[ sym (assoc _ _ _) ]
      (inv (inv f) ∘ inv f) ∘ f ≈[ ∘-cong (left-inv _) refl ]
      id ∘ f                    ≈[ left-id _ ]
      f
    qed

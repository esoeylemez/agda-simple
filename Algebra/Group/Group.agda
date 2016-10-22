-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Algebra.Group.Group where

open import Algebra.Category
open import Algebra.Group.Monoid
open import Algebra.Group.Semigroup
open import Core


-- A group is a monoid where every element has an inverse.

record IsGroup {a r} (S : Semigroup {a} {r}) : Set (a ⊔ r) where
  open Semigroup S

  field isMonoid : IsMonoid S
  open IsMonoid isMonoid

  field iso : ∀ x → Iso x

  inv : A → A
  inv x = Iso.inv (iso x)

  field inv-cong : ∀ {x y} → x ≈ y → inv x ≈ inv y

  groupoid : Groupoid
  groupoid =
    record {
      category = category;
      iso = iso;
      inv-cong = inv-cong
    }

  open Groupoid groupoid public
    using (inv-invol)


record Group {a r} : Set (lsuc (a ⊔ r)) where
  field semigroup : Semigroup {a} {r}
  open Semigroup semigroup public

  field isGroup : IsGroup semigroup
  open IsGroup isGroup public

  monoid : Monoid
  monoid =
    record {
      semigroup = semigroup;
      isMonoid = isMonoid
    }


-- A group morphism is a function that maps the elements of one group to
-- another while preserving the compositional structure, the identity
-- and all inverses.

record GroupMorphism
           {ga gr ha hr}
           (G : Group {ga} {gr})
           (H : Group {ha} {hr})
           : Set (ga ⊔ gr ⊔ ha ⊔ hr)
       where

  private
    module G = Group G
    module H = Group H

  field monoidMorphism : MonoidMorphism G.monoid H.monoid
  open MonoidMorphism monoidMorphism public

  field inv-preserving : ∀ x → map (G.inv x) H.≈ H.inv (map x)

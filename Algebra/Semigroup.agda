-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Algebra.Semigroup where

open import Algebra.Category
open import Algebra.Relation
open import Algebra.Semigroupoid
open import Core


-- A semigroup is an associative binary function.

record Semigroup {a} {r} : Set (lsuc (a ⊔ r)) where
  field
    A  : Set a
    Eq : Equiv r A

  open Equiv Eq public

  field
    _⋄_ : A → A → A
    ⋄-cong : ∀ {x1 x2 y1 y2} → x1 ≈ x2 → y1 ≈ y2 → x1 ⋄ y1 ≈ x2 ⋄ y2
    assoc  : ∀ x y z → (x ⋄ y) ⋄ z ≈ x ⋄ (y ⋄ z)

  semigroupoid : Semigroupoid
  semigroupoid =
    record {
      Ob = ⊤;
      Hom = λ _ _ → A;
      Eq = Eq;
      _∘_ = _⋄_;
      ∘-cong = ⋄-cong;
      assoc = assoc
    }


-- A semigroup morphism is a function that maps the elements of one
-- semigroup to another while preserving the compositional structure.

record SemigroupMorphism
       {sa sr ta tr}
       (S : Semigroup {sa} {sr})
       (T : Semigroup {ta} {tr})
       : Set (sa ⊔ ta ⊔ sr ⊔ tr)
       where

  private
    module S = Semigroup S
    module T = Semigroup T

  field
    map : S.A → T.A
    map-cong : ∀ {x y} → x S.≈ y → map x T.≈ map y
    ⋄-preserving : ∀ x y → map (x S.⋄ y) T.≈ map x T.⋄ map y

  semifunctor : Semifunctor S.semigroupoid T.semigroupoid
  semifunctor =
    record {
      F = λ _ → tt;
      map = map;
      map-cong = map-cong;
      ∘-preserving = ⋄-preserving
    }


-- An equivalence relation on semigroup morphisms.

SemigroupMorphismEq :
  ∀ {sa sr ta tr}
    {S : Semigroup {sa} {sr}} {T : Semigroup {ta} {tr}}
  → Equiv _ (SemigroupMorphism S T)
SemigroupMorphismEq {T = T} =
  record {
    _≈_ = λ F G →
            let module F = SemigroupMorphism F
                module G = SemigroupMorphism G
            in ∀ x → F.map x ≈ G.map x;
    refl = λ _ → refl;
    sym = λ x≈y x → sym (x≈y x);
    trans = λ x≈y y≈z x → trans (x≈y x) (y≈z x)
  }

  where
  module T = Semigroup T
  open Equiv T.Eq


-- The category of semigroups and semigroup morphisms.

Semigroups : ∀ {a r} → Category
Semigroups {a} {r} =
  record {
    semigroupoid = record {
      Ob = Semigroup {a} {r};
      Hom = SemigroupMorphism;
      Eq = SemigroupMorphismEq;
      _∘_ = _∘_;
      ∘-cong = λ {_} {_} {_} {F1} {F2} {G1} {G2} → ∘-cong {F1 = F1} {F2} {G1} {G2};
      assoc = assoc
    };
    id = id;
    left-id = left-right-id;
    right-id = left-right-id
  }

  where
  open module MyEquiv {S} {T} = Equiv (SemigroupMorphismEq {S = S} {T = T})

  _∘_ : ∀ {S T U} → SemigroupMorphism T U → SemigroupMorphism S T → SemigroupMorphism S U
  _∘_ {S} {T} {U} F G =
    record {
      map = F.map SetC.∘ G.map;
      map-cong = λ p → F.map-cong (G.map-cong p);
      ⋄-preserving = λ x y →
        begin
          F.map (G.map (x S.⋄ y))             || F.map-cong (G.⋄-preserving _ _) ::
          F.map (G.map x T.⋄ G.map y)         || F.⋄-preserving _ _ ::
          F.map (G.map x) U.⋄ F.map (G.map y)
        qed
    }

    where
    module S = Semigroup S
    module T = Semigroup T
    module U = Semigroup U
    open U.Reasoning

    module F = SemigroupMorphism F
    module G = SemigroupMorphism G

  ∘-cong :
    ∀ {S T U}
      {F1 F2 : SemigroupMorphism T U}
      {G1 G2 : SemigroupMorphism S T}
    → F1 ≈ F2 → G1 ≈ G2 → F1 ∘ G1 ≈ F2 ∘ G2
  ∘-cong {U = U} {F1} {F2} {G1} {G2} F1≈F2 G1≈G2 x =
    begin
      F1.map (G1.map x) || F1.map-cong (G1≈G2 _) ::
      F1.map (G2.map x) || F1≈F2 _ ::
      F2.map (G2.map x)
    qed

    where
    module U = Semigroup U
    open U.Reasoning

    module F1 = SemigroupMorphism F1
    module F2 = SemigroupMorphism F2
    module G1 = SemigroupMorphism G1
    module G2 = SemigroupMorphism G2

  assoc :
    ∀ {S T U V}
      (F : SemigroupMorphism U V)
      (G : SemigroupMorphism T U)
      (H : SemigroupMorphism S T)
    → (F ∘ G) ∘ H ≈ F ∘ (G ∘ H)
  assoc {V = V} _ _ _ _ = V.refl
    where
    module V = Semigroup V

  id : ∀ {S} → SemigroupMorphism S S
  id {S} =
    record {
      map = λ x → x;
      map-cong = λ x → x;
      ⋄-preserving = λ _ _ → Semigroup.refl S
    }

  left-right-id :
    ∀ {S T}
      (F : SemigroupMorphism S T)
    → F ≈ F
  left-right-id {T = T} _ _ = T.refl
    where
    module T = Semigroup T

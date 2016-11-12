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

  BimonicEq : Equiv Ob
  BimonicEq =
    record {
      _≈_ = _bimonic_;
      refl = record {
        to = id;
        from = id;
        to-monic = id-monic;
        from-monic = id-monic
      };
      sym = λ m →
        let module m = _bimonic_ m in
        record {
          to = m.from;
          from = m.to;
          to-monic = m.from-monic;
          from-monic = m.to-monic
        };
      trans = λ m1 m2 →
        let module m1 = _bimonic_ m1
            module m2 = _bimonic_ m2 in
        record {
          to = m2.to ∘ m1.to;
          from = m1.from ∘ m2.from;
          to-monic = ∘-monic m2.to-monic m1.to-monic;
          from-monic = ∘-monic m1.from-monic m2.from-monic
        }
    }

    where
    id-monic : ∀ {A} → Monic (id {A})
    id-monic {g1 = g1} {g2} p =
      begin
        g1       ≈[ sym (left-id g1) ]
        id ∘ g1  ≈[ p ]
        id ∘ g2  ≈[ left-id g2 ]
        g2
      qed

    ∘-monic :
      ∀ {A B C} {f : Hom B C} {g : Hom A B}
      → Monic f
      → Monic g
      → Monic (f ∘ g)
    ∘-monic {f = f} {g} pf pg {g1 = g1} {g2} p =
      pg $ pf $
      begin
        f ∘ (g ∘ g1)  ≈[ sym (assoc f g g1) ]
        f ∘ g ∘ g1    ≈[ p ]
        f ∘ g ∘ g2    ≈[ assoc f g g2 ]
        f ∘ (g ∘ g2)
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

  record _≃_ A B : Set (h ⊔ r) where
    field
      to : Hom A B
      iso : Iso to

    open Iso iso public

  IsoEq : Equiv Ob
  IsoEq =
    record {
      _≈_ = _≃_;
      refl = irefl;
      sym = isym;
      trans = itrans
    }

    where
    irefl : ∀ {A} → A ≃ A
    irefl =
      record {
        to = id;
        iso = record {
          inv = id;
          left-inv = left-id id;
          right-inv = left-id id
        }
      }

    isym : ∀ {A B} → A ≃ B → B ≃ A
    isym iso =
      record {
        to = iso.inv;
        iso = record {
          inv = iso.to;
          left-inv = iso.right-inv;
          right-inv = iso.left-inv
        }
      }

      where
      module iso = _≃_ iso

    itrans : ∀ {A B C} → A ≃ B → B ≃ C → A ≃ C
    itrans iso1 iso2 =
      record {
        to = iso2.to ∘ iso1.to;
        iso = record {
          inv = iso1.inv ∘ iso2.inv;
          left-inv =
            begin
              iso1.inv ∘ iso2.inv ∘ (iso2.to ∘ iso1.to)   ≈[ assoc iso1.inv iso2.inv (iso2.to ∘ iso1.to) ]
              iso1.inv ∘ (iso2.inv ∘ (iso2.to ∘ iso1.to)) ≈[ ∘-cong refl (sym (assoc iso2.inv iso2.to iso1.to)) ]
              iso1.inv ∘ (iso2.inv ∘ iso2.to ∘ iso1.to)   ≈[ ∘-cong refl (∘-cong iso2.left-inv refl) ]
              iso1.inv ∘ (id ∘ iso1.to)                   ≈[ ∘-cong refl (left-id iso1.to) ]
              iso1.inv ∘ iso1.to                          ≈[ iso1.left-inv ]
              id
            qed;
          right-inv =
            begin
              iso2.to ∘ iso1.to ∘ (iso1.inv ∘ iso2.inv)   ≈[ assoc iso2.to iso1.to (iso1.inv ∘ iso2.inv) ]
              iso2.to ∘ (iso1.to ∘ (iso1.inv ∘ iso2.inv)) ≈[ ∘-cong refl (sym (assoc iso1.to iso1.inv iso2.inv)) ]
              iso2.to ∘ (iso1.to ∘ iso1.inv ∘ iso2.inv)   ≈[ ∘-cong refl (∘-cong iso1.right-inv refl) ]
              iso2.to ∘ (id ∘ iso2.inv)                   ≈[ ∘-cong refl (left-id iso2.inv) ]
              iso2.to ∘ iso2.inv                          ≈[ iso2.right-inv ]
              id
            qed
        }
      }

      where
      module iso1 = _≃_ iso1
      module iso2 = _≃_ iso2

  Iso→Epic : ∀ {A B} {f : Hom A B} → Iso f → Epic f
  Iso→Epic {f = f} iso {g1 = g1} {g2} p =
    begin
      g1                  ≈[ sym (right-id g1) ]
      g1 ∘ id             ≈[ ∘-cong refl (sym iso.right-inv) ]
      g1 ∘ (f ∘ iso.inv)  ≈[ sym (assoc g1 f iso.inv) ]
      g1 ∘ f ∘ iso.inv    ≈[ ∘-cong p refl ]
      g2 ∘ f ∘ iso.inv    ≈[ assoc g2 f iso.inv ]
      g2 ∘ (f ∘ iso.inv)  ≈[ ∘-cong refl iso.right-inv ]
      g2 ∘ id             ≈[ right-id g2 ]
      g2
    qed

    where
    module iso = Iso iso

  Iso→Monic : ∀ {A B} {f : Hom A B} → Iso f → Monic f
  Iso→Monic {f = f} iso {g1 = g1} {g2} p =
    begin
      g1                 ≈[ sym (left-id g1) ]
      id ∘ g1            ≈[ ∘-cong (sym iso.left-inv) refl ]
      iso.inv ∘ f ∘ g1   ≈[ assoc iso.inv f g1 ]
      iso.inv ∘ (f ∘ g1) ≈[ ∘-cong refl p ]
      iso.inv ∘ (f ∘ g2) ≈[ sym (assoc iso.inv f g2) ]
      iso.inv ∘ f ∘ g2   ≈[ ∘-cong iso.left-inv refl ]
      id ∘ g2            ≈[ left-id g2 ]
      g2
    qed

    where
    module iso = Iso iso


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
      Eq = λ {A B} → FuncEq A B;
      _∘_ = _∘_;
      ∘-cong = ∘-cong;
      assoc = λ _ _ _ _ → PropEq.refl
    };
    id = λ x → x;
    left-id = λ _ _ → PropEq.refl;
    right-id = λ _ _ → PropEq.refl
  }

  where
  open module MyEquiv {A} {B} = Equiv (FuncEq A B)

  _∘_ : {A B C : Set r} (f : B → C) (g : A → B) → A → C
  (f ∘ g) x = f (g x)

  infixl 6 _∘_

  ∘-cong :
    ∀ {A B C}
      {f1 f2 : B → C} {g1 g2 : A → B}
    → f1 ≈ f2 → g1 ≈ g2 → f1 ∘ g1 ≈ f2 ∘ g2
  ∘-cong {f1 = f1} f1≈f2 g1≈g2 x =
    PropEq.trans (cong f1 (g1≈g2 _)) (f1≈f2 _)

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


surjective→epic :
  ∀ {a} {A B : Set a}
    {f : A → B}
  → (∀ y → ∃ (λ x → f x ≡ y))
  → Sets.Epic f
surjective→epic {f = f} surj {g1 = g1} {g2} p y with surj y
surjective→epic {f = f} surj {g1 = g1} {g2} p y | x , q =
  begin
    g1 y      ≈[ cong g1 (sym q) ]
    g1 (f x)  ≈[ p x ]
    g2 (f x)  ≈[ cong g2 q ]
    g2 y
  qed

  where
  open module MyEquiv {A} = Equiv (PropEq A)

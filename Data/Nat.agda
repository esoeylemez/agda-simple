-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Data.Nat where

open import Algebra.Category
open import Algebra.Relation
open import Agda.Builtin.FromNat
open import Agda.Builtin.Nat
open import Agda.Builtin.Nat public
  renaming (Nat to ℕ)
  using (suc; zero)
open import Agda.Builtin.Nat public
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
  using ()
open import Core
open import Equality


instance
  ℕ-Number : Number ℕ
  ℕ-Number =
    record {
      Constraint = λ _ → ⊤;
      fromNat = λ n → n
    }


module ℕ-Props where
  open Equiv (PropEq ℕ)
  open Reasoning

  +-assoc : ∀ x y z → (x + y) + z ≈ x + (y + z)
  +-assoc zero y z = refl
  +-assoc (suc x) y z = cong suc (+-assoc x y z)

  +-right-id : ∀ x → x + 0 ≈ x
  +-right-id zero = refl
  +-right-id (suc x) = cong suc (+-right-id x)

  +-comm : ∀ x y → x + y ≈ y + x
  +-comm zero y = sym (+-right-id y)
  +-comm (suc x) y =
    begin
      suc x + y || cong suc (+-comm x y) ::
      suc y + x || sym (one-comm y x) ::
      y + suc x
    qed

    where
    one-comm : ∀ x y → x + suc y ≈ suc x + y
    one-comm zero _ = refl
    one-comm (suc x) y = cong suc (one-comm x y)

  rdistrib-*-+ : ∀ a b x → (a + b) * x ≈ a * x + b * x
  rdistrib-*-+ zero b x = refl
  rdistrib-*-+ (suc a) b x =
    begin
      x + (a + b) * x     || cong (_+_ x) (rdistrib-*-+ a b x) ::
      x + (a * x + b * x) || sym (+-assoc x (a * x) (b * x)) ::
      (x + a * x) + b * x
    qed

  *-assoc : ∀ x y z → (x * y) * z ≈ x * (y * z)
  *-assoc zero y z = refl
  *-assoc (suc x) y z =
    begin
      (y + x * y) * z     || rdistrib-*-+ y (x * y) z ::
      y * z + (x * y) * z || cong (y * z +_) (*-assoc x y z) ::
      y * z + x * (y * z)
    qed

  *-right-id : ∀ x → x * 1 ≈ x
  *-right-id zero = refl
  *-right-id (suc x) = cong suc (*-right-id x)


ℕ-+ : Category
ℕ-+ =
  record {
    semigroupoid = record {
      Ob = ⊤;
      Hom = λ _ _ → ℕ;
      Eq = PropEq _;
      _∘_ = _+_;
      ∘-cong = cong2 _+_;
      assoc = λ {_} {_} {_} {_} {x} {y} {z} → ℕ-Props.+-assoc x y z
    };
    id = 0;
    left-id = refl;
    right-id = λ {_} {_} {x} → ℕ-Props.+-right-id x
  }

  where
  open Equiv (PropEq ℕ)

module + = Category ℕ-+


ℕ-* : Category
ℕ-* =
  record {
    semigroupoid = record {
      Ob = ⊤;
      Hom = λ _ _ → ℕ;
      Eq = PropEq ℕ;
      _∘_ = _*_;
      ∘-cong = cong2 _*_;
      assoc = λ {_} {_} {_} {_} {x} {y} {z} → ℕ-Props.*-assoc x y z
    };
    id = 1;
    left-id = λ {_} {_} {x} → ℕ-Props.+-right-id x;
    right-id = λ {_} {_} {x} → ℕ-Props.*-right-id x
  }

module * = Category ℕ-+

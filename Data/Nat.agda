-- Copyright:  (c) 2016 Ertugrul Söylemez
-- License:    BSD3
-- Maintainer: Ertugrul Söylemez <esz@posteo.de>

module Data.Nat where

open import Algebra.Group
open import Core
open import Data.Nat.Core
open import Data.Nat.Core public
  using (ℕ; ℕ-Number; suc; zero)


ℕ,+ : Monoid
ℕ,+ =
  record {
    semigroup = record {
      A = ℕ;
      Eq = PropEq ℕ;
      semigroupOver = record {
        _⋄_ = _+_;
        ⋄-cong = cong2 _+_;
        assoc = Props.+-assoc
      }
    };
    isMonoid = record {
      id = 0;
      left-id = Props.+-left-id;
      right-id = Props.+-right-id
    }
  }

module ℕ,+ = Monoid ℕ,+


ℕ,* : Monoid
ℕ,* =
  record {
    semigroup = record {
      A = ℕ;
      Eq = PropEq ℕ;
      semigroupOver = record {
        _⋄_ = _*_;
        ⋄-cong = cong2 _*_;
        assoc = Props.*-assoc
      }
    };
    isMonoid = record {
      id = 1;
      left-id = Props.*-left-id;
      right-id = Props.*-right-id
    }
  }

module ℕ,* = Monoid ℕ,*


ℕ,≤ : TotalOrder ℕ
ℕ,≤ =
  record {
    partialOrder = record {
      Eq = PropEq ℕ;
      _≤_ = _≤_;
      antisym = antisym;
      refl' = refl';
      trans = trans
    };
    total = total
  }

  where
  module P = Equiv (PropEq ℕ)

  data _≤_ : ℕ → ℕ → Set where
    0≤s : ∀ {y} → 0 ≤ y
    s≤s : ∀ {x y} → x ≤ y → suc x ≤ suc y

  antisym : {x y : ℕ} → x ≤ y → y ≤ x → x ≡ y
  antisym 0≤s 0≤s = P.refl
  antisym (s≤s p) (s≤s q) = cong suc (antisym p q)

  refl' : {x y : ℕ} → x ≡ y → x ≤ y
  refl' {zero} ≡-refl = 0≤s
  refl' {suc x} ≡-refl = s≤s (refl' ≡-refl)

  trans : {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  trans 0≤s q = 0≤s
  trans (s≤s p) (s≤s q) = s≤s (trans p q)

  total : (x y : ℕ) → Either (x ≤ y) (y ≤ x)
  total zero y = Left 0≤s
  total (suc x) zero = Right 0≤s
  total (suc x) (suc y) with total x y
  total (suc x) (suc y) | Left p = Left (s≤s p)
  total (suc x) (suc y) | Right p = Right (s≤s p)
